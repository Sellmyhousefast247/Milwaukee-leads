#!/usr/bin/env python3
"""
Milwaukee County (Wisconsin) Motivated Seller Lead Scraper
==========================================================
Cloned from the Bexar County system; same pipeline:
    scrape -> normalize -> hash/dedupe -> NEW/CHANGED detection -> score -> export

County-specific sources (Milwaukee's recorder runs on Fidlar Tapestry/Laredo,
which is pay-walled, so the equivalent motivated-seller instruments come from
Wisconsin's court + county GIS systems, which are free and structured):

  Court records : https://wcca.wicourts.gov/jsonPost/advancedCaseSearch
                  (Milwaukee = countyNo 40)
      - CV classCode 30404  -> Foreclosure of Mortgage       (cat FC)
      - CV classCode 30301  -> Money Judgment                (cat JUD)
      - TJ                  -> Transcript of Judgment        (cat JUD)
      - TW                  -> State Tax Warrant / tax lien  (cat LIEN)
      - PR                  -> Probate / estate (60-day)     (cat PRO)
  Sheriff sales : https://lio.milwaukeecountywi.gov/arcgis/rest/services/
                  Sheriff/SheriffSales/FeatureServer/0  (upcoming sales, cat FC)
  Parcel data   : https://lio.milwaukeecountywi.gov/arcgis/rest/services/
                  PropertyInfo/Parcels_w_Officials/FeatureServer/0
                  (Owner_1/2/3, Owner_Addr = mailing, Parcel_Addr, Parcel_Zip)
  Assessor      : City of Milwaukee MPROP open-data datastore (fallback)
                  https://data.milwaukee.gov/api/3/action/datastore_search

Run:
    python scraper/fetch.py                # default 7-day lookback
    python scraper/fetch.py --days 14
    python scraper/fetch.py --skip-parcel
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import logging
import os
import random
import re
import time
from dataclasses import asdict, dataclass, field
from datetime import datetime, timedelta
from pathlib import Path

import requests

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
COUNTY = "Milwaukee"
STATE = "WI"
COUNTY_NO = 40  # WCCA county number for Milwaukee

WCCA_URL = "https://wcca.wicourts.gov/jsonPost/advancedCaseSearch"
WCCA_CASE_URL = "https://wcca.wicourts.gov/caseDetail.html?caseNo={case_no}&countyNo=40"

LIO_BASE = "https://lio.milwaukeecountywi.gov/arcgis/rest/services"
SHERIFF_API_URL = f"{LIO_BASE}/Sheriff/SheriffSales/FeatureServer/0/query"
PARCEL_API_URL = f"{LIO_BASE}/PropertyInfo/Parcels_w_Officials/FeatureServer/0/query"

MPROP_API_URL = "https://data.milwaukee.gov/api/3/action/datastore_search_sql"
MPROP_RESOURCE = "0a2c7f31-cd15-4151-8222-09dd57d5f16d"

LOOKBACK_DAYS = int(os.getenv("LOOKBACK_DAYS", "7"))
PROBATE_LOOKBACK_DAYS = 60   # probate filings move slow; widen window
REQUEST_TIMEOUT = 30
RETRY_COUNT = 3
RETRY_DELAY = 3
WCCA_SLICE_DAYS = 7          # keep every WCCA query window small (result cap safety)
MPROP_MAX_AMBIGUOUS = 3      # leave address blank if MPROP returns >N matches
MPROP_MAX_LOOKUPS = 400      # cap per-record MPROP fallback to bound runtime
ARCGIS_MAX_LOOKUPS = 1500    # cap per-record ArcGIS owner/address lookups

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36")

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)-8s %(message)s",
    datefmt="%H:%M:%S",
)
log = logging.getLogger("milwaukee_scraper")

# ---------------------------------------------------------------------------
# Search definitions -> (case type, class code, category code, human label)
# The recorder-equivalent "document types" for Milwaukee are court filings;
# these are the WCCA advanced-search codes discovered from the live portal.
# Probate runs with the wider lookback window.
# ---------------------------------------------------------------------------
WCCA_QUERIES = [
    ("CV", "30404", "FC",   "Foreclosure of Mortgage"),
    ("CV", "30301", "JUD",  "Money Judgment"),
    ("TJ", None,    "JUD",  "Transcript of Judgment"),
    ("TW", None,    "LIEN", "State Tax Warrant"),
    ("PR", None,    "PRO",  "Probate / Estate"),
]
PROBATE_TYPES = {"PR"}
PROBATE_CATS = {"PRO"}

# ---------------------------------------------------------------------------
# Data model  (identical to Bexar -- required by the dashboard data contract)
# ---------------------------------------------------------------------------
GHL_FIELDS = [
    "doc_num","doc_type","cat","cat_label","filed","owner","grantee",
    "amount","prop_address","prop_city","prop_state","prop_zip",
    "mail_address","mail_city","mail_state","mail_zip","legal","clerk_url","score","flags",
    "first_seen","status",
]
GHL_HEADERS = {f: f.replace("_", " ").title() for f in GHL_FIELDS}
GHL_HEADERS["first_seen"] = "Date Entered System"
GHL_HEADERS["status"] = "Status"

@dataclass
class LeadRecord:
    doc_num: str = ""
    doc_type: str = ""
    cat: str = ""
    cat_label: str = ""
    filed: str = ""
    owner: str = ""
    grantee: str = ""
    amount: float = 0.0
    legal: str = ""
    prop_address: str = ""
    prop_city: str = ""
    prop_state: str = STATE
    prop_zip: str = ""
    mail_address: str = ""
    mail_city: str = ""
    mail_state: str = STATE
    mail_zip: str = ""
    clerk_url: str = ""
    flags: list = field(default_factory=list)
    score: int = 0
    status: str = ""
    first_seen: str = ""
    rid: str = ""
    content_hash: str = ""

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def normalize_date(raw: str) -> str:
    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y"):
        try:
            return datetime.strptime(str(raw).strip(), fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    return str(raw).strip()


def _norm_ws(s) -> str:
    return re.sub(r"\s+", " ", str(s or "").strip())


def _sql_lit(s: str) -> str:
    return s.upper().replace("'", "''")


ENTITY_PAT = re.compile(
    r"\b(LLC|L\.L\.C\.|INC|INCORPORATED|CORP|CORPORATION|LTD|LP|LLP|"
    r"BANK|MORTGAGE|LENDERS?|CREDIT UNION|FINANCIAL|FUND|TRUST|ESTATE OF|"
    r"ASSOCIATION|COMPANY|CO\.|ENTERPRISES|HOLDINGS|PARTNERS|GROUP|"
    r"N\.?A\.?$|PLLC|PC|CITY OF|COUNTY OF|STATE OF|DEPT|DEPARTMENT|"
    r"AUTHORITY|CHURCH|MINISTRIES|PROPERTIES|INVESTMENTS|VENTURES)\b",
    re.IGNORECASE,
)

def is_entity(name: str) -> bool:
    return bool(ENTITY_PAT.search(name or ""))


AKA_PAT = re.compile(r"\s+(?:a/?k/?a|f/?k/?a|d/?b/?a|n/?k/?a)\s+.*$", re.IGNORECASE)
ETAL_PAT = re.compile(r"\s*,?\s*et\s+al\.?\s*$", re.IGNORECASE)
CORPID_PAT = re.compile(r"^Corp ID:\s*\S+\s+", re.IGNORECASE)

def defendant_from_caption(caption: str) -> str:
    """'PLAINTIFF vs. DEFENDANT et al' -> 'DEFENDANT' (first defendant only)."""
    c = _norm_ws(caption)
    m = re.split(r"\s+vs?\.\s+", c, maxsplit=1, flags=re.IGNORECASE)
    if len(m) < 2:
        return ""
    d = m[1]
    d = ETAL_PAT.sub("", d)
    d = AKA_PAT.sub("", d)
    d = CORPID_PAT.sub("", d)
    return d.strip(" ,")


def plaintiff_from_caption(caption: str) -> str:
    c = _norm_ws(caption)
    m = re.split(r"\s+vs?\.\s+", c, maxsplit=1, flags=re.IGNORECASE)
    return m[0].strip() if len(m) > 1 else ""


def owner_lookup_name(name: str) -> str:
    """Normalize a person name to the parcel layer's 'LAST FIRST' format.

    Handles 'Last, First M', 'First M Last', 'FIRST LAST'; entities are
    returned as-is (parcel Owner_1 stores entities verbatim).
    """
    n = _norm_ws(name).upper().rstrip(".")
    if not n:
        return ""
    if is_entity(n):
        return re.sub(r"[.,]", "", n)
    n = re.sub(r"\bESTATE OF\b", "", n, flags=re.IGNORECASE).strip()
    if "," in n:
        last, rest = n.split(",", 1)
        first = rest.strip().split()
        return f"{last.strip()} {first[0]}".strip() if first else last.strip()
    parts = re.sub(r"[.,]", "", n).split()
    if len(parts) >= 2:
        # 'FIRST [MIDDLE] LAST' -> 'LAST FIRST'
        return f"{parts[-1]} {parts[0]}"
    return n


# Milwaukee County municipalities + common multi-word city names for parsing
# un-delimited mailing address strings ("2656 N 71ST ST WAUWATOSA WI 53213").
MULTIWORD_CITIES = [
    "WEST ALLIS", "WEST MILWAUKEE", "SOUTH MILWAUKEE", "WHITEFISH BAY",
    "FOX POINT", "BROWN DEER", "RIVER HILLS", "OAK CREEK", "HALES CORNERS",
    "SAINT FRANCIS", "ST FRANCIS", "MENOMONEE FALLS", "NEW BERLIN",
    "ELM GROVE", "EAU CLAIRE", "GREEN BAY", "FOND DU LAC", "WISCONSIN RAPIDS",
    "STEVENS POINT", "SUN PRAIRIE", "LAS VEGAS", "LOS ANGELES", "SAN DIEGO",
    "SAN FRANCISCO", "SAN ANTONIO", "NEW YORK", "SALT LAKE CITY",
]
CITY_PREFIXES = {
    "WEST", "EAST", "NORTH", "SOUTH", "NEW", "SAINT", "ST", "FORT", "FT",
    "LAKE", "OAK", "SAN", "SANTA", "LOS", "LAS", "EL", "DE", "DES", "MOUNT",
    "MT", "PORT", "GREEN", "BROWN", "FOX", "RIVER", "WHITEFISH", "HALES",
    "MENOMONEE", "ELM", "EAU", "SUN", "GLEN", "CEDAR",
}

STREET_SUFFIXES = {
    "ST", "AVE", "AV", "RD", "DR", "LN", "BLVD", "CT", "PL", "WAY", "TER",
    "TERR", "CIR", "PKWY", "HWY", "TRL", "SQ", "PLZ", "BND", "XING", "PASS",
    "RUN", "ROW", "WALK", "PATH", "LOOP", "PT", "CV", "EXPY",
}

US_STATES = {
    "AL","AK","AZ","AR","CA","CO","CT","DE","FL","GA","HI","ID","IL","IN",
    "IA","KS","KY","LA","ME","MD","MA","MI","MN","MS","MO","MT","NE","NV",
    "NH","NJ","NM","NY","NC","ND","OH","OK","OR","PA","RI","SC","SD","TN",
    "TX","UT","VT","VA","WA","WV","WI","WY","DC","PR","VI","GU","AS","MP",
}

def parse_mail_addr(raw: str) -> tuple:
    """Parse 'STREET [CITY], ST ZIP' or 'STREET CITY ST ZIP' from the END:
    zip -> state -> city. Returns (street, city, state, zip)."""
    s = _norm_ws(raw).upper()
    if not s:
        return "", "", "", ""
    zip_code = state = city = ""
    m = re.search(r"(\d{5})[- ]?(\d{4})?\s*$", s)
    if m:
        zip_code = m.group(1)
        s = s[:m.start()].strip(" ,")
    m = re.search(r",?\s+([A-Z]{2})\s*$", s)
    if m and m.group(1) in US_STATES:
        state = m.group(1)
        s = s[:m.start()].strip(" ,")
    if "," in s:
        s, city = s.rsplit(",", 1)
        city = city.strip()
        s = s.strip()
    else:
        for mw in MULTIWORD_CITIES:
            if s.endswith(" " + mw):
                city = mw
                s = s[: -len(mw) - 1].strip()
                break
        if not city:
            toks = s.split()
            # city = tokens after the LAST street-suffix token (skip unit parts)
            idx = max((i for i, t in enumerate(toks) if t.rstrip(".") in STREET_SUFFIXES),
                      default=-1)
            tail = toks[idx + 1:] if 0 <= idx < len(toks) - 1 else []
            while tail and (tail[0] in ("#", "APT", "UNIT", "STE", "SUITE", "FL", "LOWR", "UPPR")
                            or tail[0].startswith("#")):
                tail = tail[2:] if len(tail) > 1 and not tail[0].startswith("#") else tail[1:]
            if tail:
                city = " ".join(tail)
                s = " ".join(toks[: len(toks) - len(city.split())])
            elif len(toks) >= 2 and toks[-2] in CITY_PREFIXES:
                city = " ".join(toks[-2:])
                s = " ".join(toks[:-2])
            elif toks:
                city = toks[-1]
                s = " ".join(toks[:-1])
    return s.strip(" ,"), city.title(), state, zip_code


def parse_situs_addr(raw: str) -> tuple:
    """Sheriff feed: 'STREET, CITY, WI' (zip separate) -> (street, city)."""
    s = _norm_ws(raw)
    if not s:
        return "", ""
    parts = [p.strip() for p in s.split(",") if p.strip()]
    if parts and re.fullmatch(r"(?i)WI|WISCONSIN", parts[-1]):
        parts.pop()
    city = parts.pop() if len(parts) > 1 else ""
    return ", ".join(parts), city


def retry_post_json(url: str, payload: dict, headers: dict) -> dict | None:
    for attempt in range(RETRY_COUNT):
        try:
            r = requests.post(url, json=payload, headers=headers, timeout=REQUEST_TIMEOUT)
            if r.status_code == 200:
                return r.json()
            log.warning("POST %s -> HTTP %s: %s", url, r.status_code, r.text[:200])
        except Exception as exc:
            log.warning("POST error (attempt %d): %s", attempt + 1, exc)
        if attempt < RETRY_COUNT - 1:
            time.sleep(RETRY_DELAY + random.random())
    return None

# ---------------------------------------------------------------------------
# WCCA court-record scraper  (replaces Bexar's ClerkScraper; same interface)
# ---------------------------------------------------------------------------
class ClerkScraper:
    """Queries the WCCA advanced-case-search JSON API for Milwaukee County.

    Every query window is sliced into <=WCCA_SLICE_DAYS chunks so no single
    response approaches the server's result cap.
    """

    def __init__(self, default_start: datetime, default_end: datetime,
                 probate_start: datetime):
        self.default_start = default_start
        self.default_end = default_end
        self.probate_start = probate_start
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": UA,
            "Accept": "application/json",
            "Content-Type": "application/json",
            "Origin": "https://wcca.wicourts.gov",
            "Referer": "https://wcca.wicourts.gov/advanced.html",
        })

    # WCCA blocks some datacenter IP ranges (intermittent from CI runners).
    # Probe cheaply before burning full timeouts, and wait-retry the whole
    # pass a few times before giving up -- the block often clears between
    # runner sessions / over a few minutes.
    PROBE_TIMEOUT = 12
    PROBE_ATTEMPTS = 6
    PROBE_WAIT = 120

    def _alive(self) -> bool:
        payload = {
            "includeMissingDob": True, "includeMissingMiddleName": True,
            "countyNo": COUNTY_NO, "attyType": "partyAtty", "caseType": "CV",
            "classCode": "30404",
            "filingDate": {"start": self.default_end.strftime("%m-%d-%Y"),
                            "end": self.default_end.strftime("%m-%d-%Y")},
        }
        try:
            r = self.session.post(WCCA_URL, json=payload, timeout=self.PROBE_TIMEOUT)
            return r.status_code == 200
        except Exception:
            return False

    def _wait_for_wcca(self) -> bool:
        for attempt in range(1, self.PROBE_ATTEMPTS + 1):
            if self._alive():
                log.info("WCCA reachable (probe %d)", attempt)
                return True
            if attempt < self.PROBE_ATTEMPTS:
                log.warning("WCCA unreachable (probe %d/%d) -- waiting %ds",
                            attempt, self.PROBE_ATTEMPTS, self.PROBE_WAIT)
                time.sleep(self.PROBE_WAIT)
        log.error("WCCA unreachable after %d probes -- skipping court records this run",
                  self.PROBE_ATTEMPTS)
        return False

    def _slices(self, start: datetime, end: datetime):
        cur = start
        while cur <= end:
            nxt = min(cur + timedelta(days=WCCA_SLICE_DAYS - 1), end)
            yield cur, nxt
            cur = nxt + timedelta(days=1)

    def _fetch(self, case_type: str, class_code: str | None,
               start: datetime, end: datetime) -> list[dict]:
        payload = {
            "includeMissingDob": True,
            "includeMissingMiddleName": True,
            "countyNo": COUNTY_NO,
            "attyType": "partyAtty",
            "caseType": case_type,
            "filingDate": {
                "start": start.strftime("%m-%d-%Y"),
                "end": end.strftime("%m-%d-%Y"),
            },
        }
        if class_code:
            payload["classCode"] = class_code
        data = None
        for attempt in range(RETRY_COUNT):
            try:
                r = self.session.post(WCCA_URL, json=payload, timeout=REQUEST_TIMEOUT)
                if r.status_code == 200:
                    data = r.json()
                    break
                log.warning("WCCA %s -> HTTP %s: %s", case_type, r.status_code, r.text[:200])
            except Exception as exc:
                log.warning("WCCA %s error (attempt %d): %s", case_type, attempt + 1, exc)
            if attempt < RETRY_COUNT - 1:
                time.sleep(RETRY_DELAY + random.random())
        if not data:
            self._consec_fail = getattr(self, "_consec_fail", 0) + 1
            return []
        self._consec_fail = 0
        if data.get("error"):
            log.warning("WCCA %s API error: %s", case_type, data["error"])
        cases = (data.get("result") or {}).get("cases") or []
        return cases

    def run(self) -> list[LeadRecord]:
        if not self._wait_for_wcca():
            return []
        seen: set[str] = set()
        records: list[LeadRecord] = []
        for case_type, class_code, cat, cat_label in WCCA_QUERIES:
            start = self.probate_start if case_type in PROBATE_TYPES else self.default_start
            code_str = f"{case_type}" + (f"/{class_code}" if class_code else "")
            count = 0
            for s, e in self._slices(start, self.default_end):
                if getattr(self, "_consec_fail", 0) >= 3:
                    log.warning("WCCA: 3 consecutive failures -- re-probing")
                    self._consec_fail = 0
                    if not self._wait_for_wcca():
                        log.error("WCCA lost mid-run -- aborting remaining court queries")
                        return records
                cases = self._fetch(case_type, class_code, s, e)
                if len(cases) >= 400:
                    log.warning("WCCA %s %s..%s returned %d cases -- possible cap",
                                code_str, s.date(), e.date(), len(cases))
                for c in cases:
                    case_no = _norm_ws(c.get("caseNo"))
                    if not case_no or case_no in seen:
                        continue
                    seen.add(case_no)
                    caption = _norm_ws(c.get("caption"))
                    party = _norm_ws(c.get("partyName"))
                    if cat == "PRO":
                        owner = party or caption.replace("In the Estate of", "").strip()
                        grantee = ""
                    else:
                        owner = defendant_from_caption(caption) or party
                        grantee = plaintiff_from_caption(caption) or party
                    rec = LeadRecord(
                        doc_num=case_no,
                        doc_type=f"{case_type} - {cat_label}",
                        cat=cat, cat_label=cat_label,
                        filed=normalize_date(c.get("filingDate") or ""),
                        owner=owner, grantee=grantee,
                        legal=caption,
                        clerk_url=WCCA_CASE_URL.format(case_no=case_no),
                    )
                    records.append(rec)
                    count += 1
                time.sleep(0.5 + random.random() * 0.3)
            log.info("  -> %d unique records for '%s'", count, code_str)
        log.info("WCCA: %d unique records collected", len(records))
        return records

# ---------------------------------------------------------------------------
# Sheriff-sale feed (upcoming mortgage-foreclosure sales, county GIS layer)
# ---------------------------------------------------------------------------
def _expand_case_no(raw: str) -> str:
    """'24CV002413' -> '2024CV002413' (Case_Url uses the long form)."""
    s = _norm_ws(raw).upper()
    m = re.match(r"^(\d{2})([A-Z]{2}\d+)$", s)
    if m:
        return f"20{m.group(1)}{m.group(2)}"
    return s


def fetch_foreclosure_gis(start, end) -> list[LeadRecord]:
    records = []
    params = {
        "where": "1=1",
        "outFields": ("Sale_Date,Sale_Status,Plaintiff,Defendant,Case_No,"
                      "Case_Url,Addr,Zip,Muni_Name,Parcel_ID_LIO,Adjournment_Date"),
        "returnGeometry": "false",
        "resultRecordCount": 2000,
        "f": "json",
    }
    try:
        r = requests.get(SHERIFF_API_URL, params=params, timeout=REQUEST_TIMEOUT,
                         headers={"User-Agent": UA})
        features = r.json().get("features", []) or []
        log.info("SheriffSales layer: %d features", len(features))
        for feat in features:
            att = feat.get("attributes", {}) or {}
            status = _norm_ws(att.get("Sale_Status"))
            if status and status.upper() not in ("ACTIVE", "SCHEDULED", "ADJOURNED"):
                continue
            case_no = _expand_case_no(att.get("Case_No") or "")
            sale_ms = att.get("Sale_Date")
            filed = ""
            if sale_ms:
                try:
                    filed = datetime.utcfromtimestamp(sale_ms / 1000).strftime("%Y-%m-%d")
                except Exception:
                    filed = ""
            street, city = parse_situs_addr(att.get("Addr") or "")
            owner = ETAL_PAT.sub("", _norm_ws(att.get("Defendant"))).strip(" ,")
            rec = LeadRecord(
                doc_num=case_no,
                doc_type="SHERIFF SALE",
                cat="FC",
                cat_label=f"Sheriff Sale ({status or 'Scheduled'})",
                filed=filed,
                owner=owner,
                grantee=_norm_ws(att.get("Plaintiff")),
                legal=f"Sheriff sale {filed} | Taxkey {att.get('Parcel_ID_LIO') or ''}",
                prop_address=street,
                prop_city=city or _norm_ws(att.get("Muni_Name")),
                prop_state=STATE,
                prop_zip=_norm_ws(att.get("Zip")),
                clerk_url=_norm_ws(att.get("Case_Url")) or WCCA_CASE_URL.format(case_no=case_no),
            )
            rec.taxkey = _norm_ws(att.get("Parcel_ID_LIO"))  # transient, for enrichment
            if rec.prop_address or rec.owner:
                records.append(rec)
        log.info("SheriffSales usable records: %d", len(records))
    except Exception as exc:
        log.warning("SheriffSales error: %s", exc)
    return records

# ---------------------------------------------------------------------------
# Parcel enrichment (county ArcGIS) + MPROP assessor fallback
# ---------------------------------------------------------------------------
PARCEL_OUTFIELDS = "Taxkey,Owner_1,Owner_2,Owner_3,Owner_Addr,Parcel_Addr,Parcel_Zip,MuniName"


def _arcgis_query(session, where: str, count: int = 5) -> list:
    params = {
        "where": where,
        "outFields": PARCEL_OUTFIELDS,
        "returnGeometry": "false",
        "f": "json",
        "resultRecordCount": count,
    }
    try:
        r = session.get(PARCEL_API_URL, params=params, timeout=REQUEST_TIMEOUT)
        return r.json().get("features", []) or []
    except Exception as exc:
        log.debug("ArcGIS query error: %s", exc)
        return []


def _apply_parcel(rec: LeadRecord, att: dict, fill_prop: bool) -> None:
    if fill_prop and not rec.prop_address:
        situs = _norm_ws(att.get("Parcel_Addr"))
        if situs:
            rec.prop_address = situs
            rec.prop_city = _norm_ws(att.get("MuniName")) or rec.prop_city
            rec.prop_zip = _norm_ws(att.get("Parcel_Zip")) or rec.prop_zip
    if not rec.mail_address:
        ms, mc, mst, mz = parse_mail_addr(att.get("Owner_Addr") or "")
        if ms:
            rec.mail_address, rec.mail_city = ms, mc
            rec.mail_state, rec.mail_zip = mst or STATE, mz


def _addr_key(addr: str) -> tuple:
    m = re.match(r"\s*(\d+)\s+(.*)", addr or "")
    if not m:
        return "", ""
    num = m.group(1)
    rest = _norm_ws(m.group(2))
    rest = re.sub(r"^(\d+\s*-\s*)", "", rest)  # '4805 - 4811 W ...' ranges
    rest = re.sub(r"\s+(#|APT|UNIT|STE|SUITE|BLDG|LOT)\b.*$", "", rest, flags=re.I).strip()
    return num, rest


def enrich_parcels(records: list, use_mprop: bool = True) -> None:
    session = requests.Session()
    session.headers["User-Agent"] = UA

    # PASS 0 -- exact taxkey join for sheriff-sale records.
    tk = [r for r in records if getattr(r, "taxkey", "") ]
    log.info("ArcGIS taxkey-join for %d records...", len(tk))
    tk_hits = 0
    for rec in tk:
        feats = _arcgis_query(session, f"Taxkey='{_sql_lit(rec.taxkey)}'", count=1)
        if feats:
            att = feats[0].get("attributes", {})
            if not rec.owner:
                rec.owner = _norm_ws(att.get("Owner_1"))
            _apply_parcel(rec, att, fill_prop=True)
            if rec.mail_address:
                tk_hits += 1
        time.sleep(0.12)
    log.info("ArcGIS taxkey-join: %d mailing fills", tk_hits)

    # PASS 1 -- forward by owner name.
    fwd = [r for r in records if r.owner and (not r.prop_address or not r.mail_address)]
    log.info("ArcGIS owner-lookup for %d records...", len(fwd))
    owner_hits = 0
    for rec in fwd[:ARCGIS_MAX_LOOKUPS]:
        name = owner_lookup_name(rec.owner)
        if not name or len(name) < 5:
            continue
        feats = _arcgis_query(session, f"Owner_1 LIKE '{_sql_lit(name)}%'")
        if not feats and " " in name and not is_entity(rec.owner):
            # retry with 'LAST FIRSTINITIAL'
            last, first = name.split(" ", 1)
            feats = _arcgis_query(session, f"Owner_1 LIKE '{_sql_lit(last)} {_sql_lit(first[:1])}%'")
        if not feats:
            continue
        att = feats[0].get("attributes", {})
        _apply_parcel(rec, att, fill_prop=(len(feats) == 1))
        if rec.mail_address:
            owner_hits += 1
        time.sleep(0.12)
    log.info("ArcGIS owner-lookup: %d fills", owner_hits)

    # PASS 2 -- reverse by address (records with an address but no owner).
    rev = [r for r in records if r.prop_address and not r.owner]
    log.info("ArcGIS address-lookup for %d records...", len(rev))
    addr_hits = 0
    for rec in rev[:ARCGIS_MAX_LOOKUPS]:
        num, core = _addr_key(rec.prop_address)
        if not num or not core:
            continue
        feats = _arcgis_query(session, f"Parcel_Addr LIKE '{_sql_lit(num)}%{_sql_lit(core)}%'")
        if len(feats) == 1:
            att = feats[0].get("attributes", {})
            owner = _norm_ws(att.get("Owner_1"))
            if owner:
                rec.owner = owner
                addr_hits += 1
            _apply_parcel(rec, att, fill_prop=False)
        time.sleep(0.12)
    log.info("ArcGIS address-lookup: %d owner fills", addr_hits)

    # PASS 3 -- MPROP assessor fallback (City of Milwaukee) for records that
    # still have an owner but no property address.
    if not use_mprop:
        return
    still_need = [r for r in records if r.owner and not r.prop_address]
    if not still_need:
        log.info("ArcGIS covered all records - skipping MPROP lookup")
        return
    if len(still_need) > MPROP_MAX_LOOKUPS:
        log.info("Capping MPROP lookups at %d (of %d unmatched)",
                 MPROP_MAX_LOOKUPS, len(still_need))
        still_need = still_need[:MPROP_MAX_LOOKUPS]
    log.info("Attempting MPROP owner-lookup for %d unmatched records...", len(still_need))
    hits = 0
    disabled = False
    for rec in still_need:
        if disabled:
            break
        name = owner_lookup_name(rec.owner)
        if not name or len(name) < 5:
            continue
        sql = (
            'SELECT "TAXKEY","OWNER_NAME_1","OWNER_MAIL_ADDR","OWNER_CITY_STATE",'
            '"OWNER_ZIP","HOUSE_NR_LO","SDIR","STREET","STTYPE","GEO_ZIP_CODE" '
            f'FROM "{MPROP_RESOURCE}" WHERE "OWNER_NAME_1" LIKE \'{_sql_lit(name)}%\' LIMIT 6'
        )
        try:
            r = session.get(MPROP_API_URL, params={"sql": sql}, timeout=REQUEST_TIMEOUT)
            j = r.json()
            if not j.get("success"):
                log.warning("MPROP SQL API unavailable -- disabling fallback: %s",
                            str(j.get("error"))[:200])
                disabled = True
                break
            rows = (j.get("result") or {}).get("records") or []
        except Exception as exc:
            log.debug("MPROP lookup error: %s", exc)
            rows = []
        strict = rec.cat in PROBATE_CATS
        limit = 1 if strict else MPROP_MAX_AMBIGUOUS
        if not rows or len(rows) > limit:
            time.sleep(0.15)
            continue
        row = rows[0]
        street = " ".join(_norm_ws(row.get(k)) for k in
                          ("HOUSE_NR_LO", "SDIR", "STREET", "STTYPE") if _norm_ws(row.get(k)))
        if street:
            rec.prop_address = street
            rec.prop_city = "Milwaukee"
            rec.prop_zip = _norm_ws(row.get("GEO_ZIP_CODE"))[:5]
        if not rec.mail_address and _norm_ws(row.get("OWNER_MAIL_ADDR")):
            cs = _norm_ws(row.get("OWNER_CITY_STATE"))
            mcity, mstate = cs[:-2].strip(" ,"), cs[-2:] if len(cs) > 2 else ""
            rec.mail_address = _norm_ws(row.get("OWNER_MAIL_ADDR"))
            rec.mail_city = mcity.title()
            rec.mail_state = mstate or STATE
            rec.mail_zip = _norm_ws(row.get("OWNER_ZIP"))[:5]
        if rec.prop_address:
            hits += 1
        time.sleep(0.15)
    log.info("MPROP enrichment: %d/%d records matched", hits, len(still_need))

# ---------------------------------------------------------------------------
# Hash / dedupe identity + NEW-CHANGED detection (pipeline stages 3-4)
# ---------------------------------------------------------------------------
def _repo_base() -> Path:
    return Path(__file__).parent.parent


def _record_rid(r) -> str:
    """Stable identity hash: doc number, else owner|filed|type|address."""
    basis = r.doc_num or f"{r.owner}|{r.filed}|{r.doc_type}|{r.prop_address}"
    return hashlib.sha1(f"milwaukee|{basis}".encode()).hexdigest()[:16]


def _record_chash(r) -> str:
    """Content hash - changes when any meaningful field changes."""
    fields = "|".join(str(x or "") for x in (
        r.doc_num, r.doc_type, r.filed, r.owner, r.grantee, r.legal,
        r.amount, r.prop_address, r.mail_address))
    return hashlib.sha1(fields.encode()).hexdigest()[:16]


def detect_changes(records: list) -> None:
    """Compare against data/state.json; stamp status + first_seen on each record."""
    state_path = _repo_base() / "data" / "state.json"
    try:
        state = json.loads(state_path.read_text(encoding="utf-8")) if state_path.exists() else {}
    except Exception:
        state = {}
    today = datetime.now().strftime("%Y-%m-%d")
    n_new = n_chg = n_exist = 0
    for r in records:
        r.rid = _record_rid(r)
        r.content_hash = _record_chash(r)
        prev = state.get(r.rid)
        if prev is None:
            r.status, r.first_seen = "NEW", today
            n_new += 1
        elif prev.get("content_hash") != r.content_hash:
            r.status = "CHANGED"
            r.first_seen = prev.get("first_seen", today)
            n_chg += 1
        else:
            r.status = "EXISTING"
            r.first_seen = prev.get("first_seen", today)
            n_exist += 1
        state[r.rid] = {"content_hash": r.content_hash,
                        "first_seen": r.first_seen, "last_seen": today}
    state_path.parent.mkdir(parents=True, exist_ok=True)
    state_path.write_text(json.dumps(state, indent=1), encoding="utf-8")
    log.info("NEW/CHANGED: NEW=%d CHANGED=%d EXISTING=%d (state=%d ids)",
             n_new, n_chg, n_exist, len(state))

# ---------------------------------------------------------------------------
# Scoring
# ---------------------------------------------------------------------------
def score_records(records: list, start: datetime) -> None:
    for r in records:
        s, flags = 30, []
        if r.cat == "LP": s += 10; flags.append("LIS_PENDENS")
        if r.cat == "FC": s += 15; flags.append("FORECLOSURE")
        if r.cat == "TAXFC": s += 18; flags.append("TAX_FORECLOSURE")
        if r.cat == "TAXDEED": s += 10; flags.append("TAX_DEED")
        if r.cat in ("LP","FC","TAXFC"): s += 5
        if r.cat == "JUD": s += 8; flags.append("JUDGMENT")
        if r.cat == "LIEN": s += 7; flags.append("LIEN")
        if r.cat == "PRO": s += 12; flags.append("PROBATE")
        if r.amount > 100000: s += 15; flags.append("HIGH_AMOUNT")
        elif r.amount > 50000: s += 10; flags.append("MID_AMOUNT")
        if r.filed:
            try:
                if datetime.strptime(r.filed, "%Y-%m-%d") >= start:
                    s += 5; flags.append("NEW_THIS_WEEK")
            except ValueError:
                pass
        if r.prop_address:
            s += 5; flags.append("HAS_ADDRESS")
        r.score = min(s, 100)
        r.flags = flags

# ---------------------------------------------------------------------------
# Outputs (dashboard data contract -- identical to Bexar)
# ---------------------------------------------------------------------------
DASH_CAT = {
    "LP": "foreclosure", "FC": "foreclosure", "TAXFC": "foreclosure",
    "TAXDEED": "tax_lien", "LIEN": "tax_lien",
    "JUD": "judgment", "PRO": "probate",
}
FLAG_NICE = {
    "LIS_PENDENS": "Lis pendens", "FORECLOSURE": "Pre-foreclosure",
    "TAX_FORECLOSURE": "Tax foreclosure", "TAX_DEED": "Tax deed",
    "JUDGMENT": "Judgment lien", "LIEN": "Tax lien",
    "PROBATE": "Probate / estate", "HIGH_AMOUNT": "Amount > $100k",
    "MID_AMOUNT": "Amount > $50k", "NEW_THIS_WEEK": "New this week",
    "HAS_ADDRESS": "Has address",
}


def write_outputs(records: list, start: datetime, end: datetime) -> None:
    base = _repo_base()
    for d in [base / "dashboard", base / "data"]:
        d.mkdir(parents=True, exist_ok=True)
    week_ago = (end - timedelta(days=7)).strftime("%Y-%m-%d")
    recs_out = []
    for r in records:
        d = asdict(r)
        d.pop("taxkey", None)
        d["cat_code"] = r.cat
        d["cat"] = DASH_CAT.get(r.cat, "tax_lien")
        d["flags"] = [FLAG_NICE.get(f, f) for f in (r.flags or [])]
        d["absentee"] = bool(
            r.prop_address and r.mail_address
            and r.prop_address.upper() != r.mail_address.upper())
        d["out_of_state"] = bool(r.mail_state and r.mail_state.upper() != STATE)
        recs_out.append(d)
    payload = {
        "fetched_at": datetime.utcnow().isoformat(),
        "county": COUNTY,
        "source": f"{COUNTY} County, {STATE} -- WCCA Courts + Sheriff Sales + Parcel API + MPROP",
        "date_range": {"start": start.strftime("%Y-%m-%d"), "end": end.strftime("%Y-%m-%d")},
        "total": len(records),
        "new_7d": sum(1 for r in records if (r.first_seen or "") >= week_ago),
        "with_address": sum(1 for r in records if r.prop_address),
        "by_cat": {c: sum(1 for r in records if r.cat == c) for c in ("FC","TAXFC","TAXDEED","LP","JUD","LIEN","PRO")},
        "records": recs_out,
    }
    for path in [base / "dashboard" / "records.json", base / "data" / "records.json"]:
        path.write_text(json.dumps(payload, indent=2, default=str))
        log.info("JSON written: %s (%d records)", path, len(records))
    csv_path = base / "data" / "ghl_export.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(GHL_HEADERS.values()))
        writer.writeheader()
        for r in records:
            d = asdict(r)
            writer.writerow({GHL_HEADERS[k]: ("|".join(d[k]) if k=="flags" else d[k]) for k in GHL_FIELDS})
    log.info("GHL CSV written: %s (%d records)", csv_path, len(records))
    skip_path = base / "data" / "skiptrace_export.csv"
    skip_cols = ["First Name", "Last Name", "Mailing Address", "Mailing City",
                 "Mailing State", "Mailing Zip", "Property Address",
                 "Property City", "Property State", "Property Zip"]
    with open(skip_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=skip_cols)
        writer.writeheader()
        for r in records:
            owner = (r.owner or "").strip()
            if "," in owner:
                p = owner.split(",", 1)
                first, last = p[1].strip().title(), p[0].strip().title()
            else:
                p = owner.split()
                first = p[0].title() if p else ""
                last = " ".join(p[1:]).title() if len(p) > 1 else ""
            writer.writerow({
                "First Name": first, "Last Name": last,
                "Mailing Address": r.mail_address, "Mailing City": r.mail_city,
                "Mailing State": r.mail_state, "Mailing Zip": r.mail_zip,
                "Property Address": r.prop_address, "Property City": r.prop_city,
                "Property State": r.prop_state, "Property Zip": r.prop_zip,
            })
    log.info("Skip trace CSV written: %s (%d records)", skip_path, len(records))

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main() -> None:
    parser = argparse.ArgumentParser(description="Milwaukee County lead scraper")
    parser.add_argument("--days", type=int, default=LOOKBACK_DAYS)
    parser.add_argument("--probate-days", type=int, default=PROBATE_LOOKBACK_DAYS)
    parser.add_argument("--skip-parcel", action="store_true")
    parser.add_argument("--skip-mprop", action="store_true")
    args = parser.parse_args()
    end = datetime.now()
    start = end - timedelta(days=args.days)
    probate_start = end - timedelta(days=args.probate_days)
    log.info("=" * 60)
    log.info("Milwaukee County Motivated Seller Lead Scraper")
    log.info("Lookback default=%dd  probate=%dd", args.days, args.probate_days)
    log.info("=" * 60)
    log.info("Range: default %s->%s | probate %s->%s",
             start.strftime("%m/%d/%Y"), end.strftime("%m/%d/%Y"),
             probate_start.strftime("%m/%d/%Y"), end.strftime("%m/%d/%Y"))
    scraper = ClerkScraper(start, end, probate_start)
    records = scraper.run()
    gis_recs = fetch_foreclosure_gis(start, end)
    existing_ids = {r.doc_num for r in records if r.doc_num}
    existing_addr = {r.prop_address.upper() for r in records if r.prop_address}
    for r in gis_recs:
        if r.doc_num and r.doc_num in existing_ids:
            continue
        if r.prop_address and r.prop_address.upper() in existing_addr:
            continue
        records.append(r)
    if not args.skip_parcel:
        enrich_parcels(records, use_mprop=not args.skip_mprop)
    detect_changes(records)
    score_records(records, start)
    records.sort(key=lambda r: (r.status != "NEW", -r.score))
    if not records:
        log.warning("No records found. Writing empty output files.")
    else:
        log.info("Total after dedup + enrichment: %d", len(records))
    write_outputs(records, start, end)
    pro_count = sum(1 for r in records if r.cat == "PRO")
    pro_with_addr = sum(1 for r in records if r.cat == "PRO" and r.prop_address)
    log.info("=" * 60)
    log.info("SUMMARY")
    log.info("  Total records  : %d", len(records))
    log.info("  With address   : %d", sum(1 for r in records if r.prop_address))
    log.info("  Probates       : %d (%d with address)", pro_count, pro_with_addr)
    log.info("  Score >= 70    : %d", sum(1 for r in records if r.score >= 70))
    log.info("  Score >= 50    : %d", sum(1 for r in records if r.score >= 50))


if __name__ == "__main__":
    main()
