#!/bin/sh
# Release build with profile-guided optimisation when the toolchain allows it.
# Every PGO step is optional: if any of them fails, this falls back to a plain release build.
FLAGS="-C target-cpu=x86-64-v3"
PGO_FLAGS=""
W=/tmp/pgo-work
if rustup component add llvm-tools >/dev/null 2>&1; then
  PD=$(ls "$(rustc --print sysroot)"/lib/rustlib/*/bin/llvm-profdata 2>/dev/null | head -1)
  if [ -n "$PD" ] \
    && (cd pgo-generator && cargo build --release --locked -q) \
    && ./pgo-generator/target/release/generate --seed 7 --events 2000000 --clicks 500000 --output $W/train >/dev/null \
    && RUSTFLAGS="$FLAGS -Cprofile-generate=$W/raw" cargo build --release --locked -q --target-dir $W/target \
    && NCPU=4 DATA_DIR=$W/train OUTPUT_DIR=$W/out $W/target/release/sessions \
    && "$PD" merge -o $W/pgo.profdata $W/raw; then
    cp $W/pgo.profdata /tmp/pgo.profdata
    PGO_FLAGS="-Cprofile-use=/tmp/pgo.profdata"
    echo "PGO: using profile"
  else
    echo "PGO: profiling step failed, plain build"
  fi
else
  echo "PGO: llvm-tools unavailable, plain build"
fi
RUSTFLAGS="$FLAGS $PGO_FLAGS" cargo build --release --locked
