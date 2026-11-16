#!/bin/sh
# In the project image: point this checkout's Lake packages at the image's prebuilt, read-only
# copy (/opt/bzip2-lake/.lake/packages) instead of cloning and unpacking Mathlib (about 7 GB)
# here. The fleet runs it at the start of every attempt (project.toml `prepare`). Outside the
# image it does nothing, and Lake fetches packages as usual. Works from any directory.
set -eu
cd "$(dirname "$0")/.."
image_packages=/opt/bzip2-lake/.lake/packages
[ -d "$image_packages" ] || exit 0
if ! cmp -s lake-manifest.json /opt/bzip2-lake/lake-manifest.json; then
  echo "use-image-packages: lake-manifest.json differs from the image's; rebuild the image" >&2
  exit 1
fi
mkdir -p .lake
if [ -L .lake/packages ] || [ ! -e .lake/packages ]; then
  ln -sfn "$image_packages" .lake/packages
fi
