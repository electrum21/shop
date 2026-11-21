# Shopping Sessions: a single Rust binary (parallel mmap CSV parse, lock-free union-find for
# links, hand-written Parquet writer). Built for linux/amd64 (x86-64-v3: AVX2/BMI2) on the scorer.
# build.sh adds profile-guided optimisation (trained on a generated dataset) when llvm-tools can
# be installed, and otherwise does a plain release build.
FROM rust:1-slim-bookworm AS build
WORKDIR /src
COPY Cargo.toml Cargo.lock build.sh ./
COPY pgo-generator ./pgo-generator
COPY src ./src
RUN sh ./build.sh

FROM debian:bookworm-slim
COPY --from=build /src/target/release/sessions /app/sessions
ENV DATA_DIR=/data OUTPUT_DIR=/output SCRATCH_DIR=/scratch HOME=/scratch
ENTRYPOINT ["/app/sessions"]
