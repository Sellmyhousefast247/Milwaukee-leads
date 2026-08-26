# Milwaukee-leads

Motivated-seller lead scraper for **Milwaukee County, WI** — cloned from the Bexar County system.

Pipeline: county sources → scrape → normalize → hash/dedupe → NEW/CHANGED detection → score → export.

**Sources**
- WCCA circuit-court records (countyNo 40): mortgage foreclosures (CV/30404), money judgments (CV/30301), transcripts of judgment (TJ), state tax warrants (TW), probate (PR, 60-day lookback)
- Milwaukee County Sheriff sale GIS feed (upcoming foreclosure auctions)
- Enrichment: Milwaukee County parcel layer (owner / situs / mailing) + City of Milwaukee MPROP assessor fallback

**Outputs**
- `dashboard/` — live dashboard (GitHub Pages) + `records.json`
- `data/ghl_export.csv` — GHL import
- `data/skiptrace_export.csv` — skip-trace list

Runs daily via GitHub Actions (13:00 UTC) and on manual dispatch.
