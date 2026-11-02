# Reproduction image for "Migrating CakeML Type Soundness from HOL4 to Lean
# with LLM Agents: An Experience Report" (FormaliSE 2027).
#
# Build:  docker build -t cakeml-lean-migration:1.0 .
# Run:    docker run --rm cakeml-lean-migration:1.0
#
# The image contains Lean 4.29.1, batteries at the commit pinned by the frozen
# baseline, Python 3, and this artifact. Running it executes run_all.sh, which
# needs no network access.
FROM debian:bookworm-slim

ARG LEAN_VERSION=4.29.1
ARG BATTERIES_REV=756e3321fd3b02a85ffda19fef789916223e578c
ARG TARGETARCH

RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git python3 unzip \
 && rm -rf /var/lib/apt/lists/*

# Lean toolchain from the official release.
RUN case "${TARGETARCH:-amd64}" in \
      amd64) LEAN_ARCH=linux ;; \
      arm64) LEAN_ARCH=linux_aarch64 ;; \
      *) echo "unsupported architecture ${TARGETARCH}"; exit 1 ;; \
    esac \
 && curl -fsSL -o /tmp/lean.zip \
      "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-${LEAN_ARCH}.zip" \
 && unzip -q /tmp/lean.zip -d /opt \
 && mv /opt/lean-${LEAN_VERSION}-* /opt/lean \
 && rm /tmp/lean.zip
ENV PATH=/opt/lean/bin:$PATH

# batteries at the pinned commit.
RUN git clone --filter=blob:none https://github.com/leanprover-community/batteries /opt/batteries \
 && git -C /opt/batteries checkout -q ${BATTERIES_REV}
ENV BATTERIES=/opt/batteries

COPY . /artifact
WORKDIR /artifact
RUN chmod +x run_all.sh scripts/run_audit.sh
CMD ["./run_all.sh"]
