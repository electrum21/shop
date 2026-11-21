# Shopping Sessions: a single static-ish Rust binary (parallel mmap CSV parse, lock-free
# union-find for links, hand-written Parquet writer). Built for linux/amd64 on the scorer.
FROM rust:1-slim-bookworm AS build
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY src ./src
RUN cargo build --release --locked

FROM debian:bookworm-slim
COPY --from=build /src/target/release/sessions /app/sessions
ENV DATA_DIR=/data OUTPUT_DIR=/output SCRATCH_DIR=/scratch HOME=/scratch
ENTRYPOINT ["/app/sessions"]
