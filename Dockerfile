# Shopping Sessions: a single Rust binary (parallel mmap CSV parse, lock-free union-find for
# links, hand-written Parquet writer). Built for linux/amd64 (x86-64-v3: AVX2/BMI2) on the scorer.
FROM rust:1-slim-bookworm AS build
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY src ./src
ENV RUSTFLAGS="-C target-cpu=x86-64-v3"
RUN cargo build --release --locked

FROM debian:bookworm-slim
COPY --from=build /src/target/release/sessions /app/sessions
ENV DATA_DIR=/data OUTPUT_DIR=/output SCRATCH_DIR=/scratch HOME=/scratch
ENTRYPOINT ["/app/sessions"]
