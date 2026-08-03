# Artifact container: Redex async/await models + differential fuzzer.
#
# FALLBACK route: the primary image is built BY nix (`nix build .#image`,
# see flake.nix) — same design, no Nix inside the container. This Dockerfile
# exists for hosts that can run docker but cannot build a Linux nix closure
# (e.g. macOS without a configured Linux builder): `docker build` runs the
# whole flake inside the container instead.
#
# Design: the Nix flake provides every toolchain EXCEPT Swift (racket,
# python 3.14 + trio, node 22, dotnet 10, rust 1.92 with vendored crates for
# offline builds). Swift 6 is not in nixpkgs, so the container BASE is the
# official swift.org Ubuntu image and Nix is installed on top — the same
# split as the native setup, where swiftc comes from the system Xcode and
# the flake's shellHook clears DEVELOPER_DIR/SDKROOT (a no-op on Linux).
#
# Build (from the REPOSITORY ROOT — the flake lives there):
#   docker build -t async-models-artifact -f artifact/docker/Dockerfile .
# Run:
#   docker run -it async-models-artifact
# The build ends with a 1-program-per-lane fuzz smoke across all 7 runtimes;
# a green build therefore already validates the whole pipeline in-container.

# 6.0.3 matches the paper's pinned Swift; -jammy = Ubuntu 22.04.
FROM swift:6.0.3-jammy

# build-essential: rustc needs a C linker (`cc`); the swift base image
# ships clang for Swift but no `cc`, which fails every cargo build.
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      curl xz-utils ca-certificates git sudo locales build-essential \
 && rm -rf /var/lib/apt/lists/* \
 && locale-gen en_US.UTF-8

ENV LANG=en_US.UTF-8 \
    DOTNET_CLI_TELEMETRY_OPTOUT=1

# Non-root user: single-user Nix wants one, and evaluators should not need
# root anyway.
RUN useradd -m -s /bin/bash artifact \
 && echo "artifact ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/artifact
USER artifact
ENV USER=artifact
WORKDIR /home/artifact

# Single-user Nix (no daemon — containers have no systemd), flakes enabled,
# sandbox off (no user namespaces inside most container runtimes).
RUN curl -L https://nixos.org/nix/install | sh -s -- --no-daemon
ENV PATH=/home/artifact/.nix-profile/bin:$PATH
RUN mkdir -p ~/.config/nix \
 && printf 'experimental-features = nix-command flakes\nsandbox = false\n' \
      > ~/.config/nix/nix.conf

# The repository (root flake + artifact/; .dockerignore excludes the paper
# and caches/results). The context may be a nix store path (image-runner
# passes the flake's own source), whose read-only modes COPY preserves —
# restore owner-writability so evaluators can create fuzz-cache/ and edit
# the tree.
COPY --chown=artifact:artifact . /home/artifact/repo
RUN chmod -R u+w /home/artifact/repo
WORKDIR /home/artifact/repo

# Realize the flake at build time so the image is self-contained offline:
#  - .#fuzz builds the model derivation (raco make -> compiled/*.zo) and
#    pulls every nix toolchain into the store;
#  - the dev shell is what evaluators will type commands in.
RUN nix build .#fuzz && nix develop --command true

# Put the artifact commands on PATH (~/.nix-profile/bin), matching the
# nix-built image's UX: `fuzz`, `run-tests`, `figs` work bare.
RUN nix profile install .#fuzz .#run-tests .#figs

# Sanity: the dev shell must see BOTH the nix toolchains and the base
# image's swiftc.
RUN nix develop --command bash -c 'swiftc --version && dotnet --version && rustc --version && racket --version'

# Build-time smoke test: one program per lane, two runtime runs. A green
# image build therefore proves the entire pipeline works in-container, and
# it warms the caches that make later runs fast and offline (the shared
# cargo target dirs under /tmp, the dotnet/NuGet first-build state). A
# failure fails the build — by design — and dumps the lane logs.
RUN fuzz -n 1 -r 2 \
 || { echo '=== lane logs ==='; tail -n 40 fuzz-cache/*/*.log; exit 1; } \
 && rm -rf fuzz-cache

# Evaluators land where the models live (redex/, figs/), with the README
# beside them; figs reads the editable in-repo figure programs.
RUN cp README.md artifact/README.md
ENV FIGS_DIR=/home/artifact/repo/artifact/figs
WORKDIR /home/artifact/repo/artifact

CMD ["bash", "-l"]
