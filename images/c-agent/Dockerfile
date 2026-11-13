# Agent image for C projects: the agent CLI plus a C toolchain, git and python3.
#
#   docker build -t afe-c-agent:pilot images/c-agent
#
# afe-fleet runs it as the worker's uid/gid with /work (the checkout), /task (read-only),
# /out and a per-attempt HOME mounted; credentials are mounted read-only by the host config.
FROM node:22-bookworm-slim

RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates git build-essential binutils python3 less \
 && rm -rf /var/lib/apt/lists/*

ARG CLAUDE_CODE_VERSION=2.1.323
RUN npm install -g @anthropic-ai/claude-code@${CLAUDE_CODE_VERSION} && npm cache clean --force

# commits made inside the container; the worker rewrites nothing, so give them an identity
ENV DISABLE_AUTOUPDATER=1 \
    GIT_AUTHOR_NAME="afe-fleet agent" GIT_AUTHOR_EMAIL="agent@afe-fleet.invalid" \
    GIT_COMMITTER_NAME="afe-fleet agent" GIT_COMMITTER_EMAIL="agent@afe-fleet.invalid"
WORKDIR /work
