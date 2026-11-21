# Shopping Sessions: Rust pipeline

One Rust binary, no runtime dependencies besides libc. Pipeline (all stages parallel over `NCPU` threads):

1. **Links**: parse `links/*.csv` in parallel, insert IDs into a lock-free open-addressing table and union them with a
   concurrent union-find that always roots a component at its byte-wise smallest ID (the person's name). The table is
   then flattened so a lookup is a single probe.
2. **Parse** events and clicks straight from `mmap`ed files, in 4 MB chunks, with an AVX2 structural scanner
   (commas/newlines/quotes as 64-bit masks; per-record quote validation) and a SWAR/cached timestamp parser.
   Person lookups are batched with prefetch. Each valid event emits a compact 24-byte record into a person bucket
   and a 24-byte (event_id, location, ingest_ts) record into an event_id bucket; clicks go to person buckets.
3. **Dedup**: per `event_id` bucket keep the copy with the smallest `ingest_ts` (rules.md order: dedup, *then*
   validate / late-drop) and mark every other valid copy as a loser in per-writer atomic bitmaps.
4. **Per person** (skipping losers): sort by `ts`, cut sessions at gaps > 30 min, credit each session to the latest click in the previous
   7 days (ties: smallest `click_id`), and compute assists per campaign with interval merging over the person's
   sessions (so whale persons stay linear). Daily user rows and per-(campaign, day) accumulators come out of this.
5. **Output**: each worker writes its own `user_daily/part-N.parquet` (hand-written Parquet writer, PLAIN,
   uncompressed); `campaign_daily/part-000.parquet` is merged at the end.

Memory for intermediate records comes from a block pool backed by `mmap` + `MADV_HUGEPAGE`/`MADV_POPULATE_WRITE`
(blocks freed after dedup are reused for the per-person records).

## Check locally

```
cargo build --release
python3 scripts/run_fixtures.py fixtures -- target/release/sessions        # 36 edge-case fixtures
generate --seed 1 --events 1000000 --clicks 250000 --output dev
DATA_DIR=dev OUTPUT_DIR=out target/release/sessions
python3 scripts/compare.py out dev-answer                                   # published dev answer
python3 scripts/ref.py dev refdev && python3 scripts/compare.py out refdev  # independent slow reference
```
`VERBOSE=1` prints stage timings to stderr.
