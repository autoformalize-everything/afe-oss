# Agent image for the bzip2 Lean formalization (afe-tasks tasks/bzip2: image = "afe-bzip2-lean:dev").
#
#   docker build -t afe-bzip2-lean:dev -f images/bzip2-lean/Dockerfile projects/bzip2
#
# For afe-fleet's container runtime (the agent CLI runs on the host; its tools run in here as the
# worker's uid). Contents: Lean, at the toolchain projects/bzip2/lean-toolchain names, in
# /opt/elan; clang with libFuzzer and a C toolchain; and the Lake dependencies of
# projects/bzip2/lake-manifest.json, Mathlib's build included, read-only in
# /opt/bzip2-lake/.lake/packages. A checkout uses those through the symlink
# projects/bzip2/.lake/packages -> /opt/bzip2-lake/.lake/packages (tools/use-image-packages.sh).
# Rebuild whenever lake-manifest.json or lean-toolchain changes. The C sources are not in the
# image: they are vendored in the repository, projects/bzip2/upstream.
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y --no-install-recommends \
      bash binutils build-essential bzip2 ca-certificates clang curl git less lld llvm libclang-rt-14-dev \
      python3 xz-utils zstd \
  && rm -rf /var/lib/apt/lists/* \
  && git config --system --add safe.directory '*'     # the packages below belong to root

ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:$PATH
COPY lean-toolchain /tmp/lean-toolchain
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --no-modify-path --default-toolchain none \
  && elan toolchain install "$(cat /tmp/lean-toolchain)" \
  && elan default "$(cat /tmp/lean-toolchain)" \
  && lean --version \
  && chmod -R a+rX /opt/elan && rm /tmp/lean-toolchain

# The Lake dependencies, built. `lake build Mathlib` only replays the cached files, but also
# builds what the cache leaves out (ProofWidgets' widget bundle), which Lake would otherwise try
# to write on first use.
COPY lakefile.toml lake-manifest.json lean-toolchain /opt/bzip2-lake/
RUN cd /opt/bzip2-lake && lake exe cache get && lake build Mathlib \
  && chmod -R a+rX /opt/bzip2-lake && chmod -R a-w /opt/bzip2-lake/.lake

# Lake runs `git diff --exit-code` in every package on every start. The chmod above changed every
# file's ctime after git recorded it in the package's index, and the agents (not root) cannot
# write the refreshed index back: git re-checked all of Mathlib's files on every `lake` run, 0.7 s
# each time. Refresh each index now, and compare only size and mtime in these repos, so the index
# also matches where the image is unpacked again (new ctimes and inodes); the packages never change.
RUN for p in /opt/bzip2-lake/.lake/packages/*/; do \
      git -C "$p" config core.checkStat minimal && git -C "$p" config core.trustctime false \
      && git -C "$p" update-index -q --refresh; done

# Login shells (`bash -lc`, which Codex runs every command in) reset PATH from /etc/profile and
# lose /opt/elan/bin: put the Lean commands where every shell finds them.
RUN ln -s /opt/elan/bin/* /usr/local/bin/
