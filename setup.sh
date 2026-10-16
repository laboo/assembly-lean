#!/usr/bin/env bash
# One-step setup for a fresh Claude workspace (Linux x86_64), where Lean's own
# download site and Mathlib's cache are blocked but GitHub works.
#   1. installs elan and Lean 4.35.0 from GitHub releases (skipped if present);
#   2. restores the compiled Mathlib (and the rest of .lake) from library/,
#      so nothing has to be rebuilt from source.
# Run from anywhere:  bash setup.sh
# Then:  export PATH=$HOME/.elan/bin:$PATH && lake build BuildingLand && lake build building && .lake/build/bin/building
set -euo pipefail
cd "$(dirname "$0")"
REPO="$PWD"

python3 -c "import zstandard" 2>/dev/null || pip install --break-system-packages -q zstandard

unzst () {  # unzst <file.tar.zst or -> <dest dir>
  python3 -I -c "
import sys, tarfile, zstandard
src = sys.stdin.buffer if sys.argv[1] == '-' else open(sys.argv[1], 'rb')
r = zstandard.ZstdDecompressor().stream_reader(src)
tarfile.open(fileobj=r, mode='r|').extractall(sys.argv[2], filter='tar')
" "$1" "$2"
}

# 1. elan and Lean 4.35.0
TC="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0"
if [ ! -x "$TC/bin/lean" ]; then
  if [ ! -x "$HOME/.elan/bin/elan" ]; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
    bash /tmp/elan-init.sh -y --default-toolchain none >/dev/null 2>&1 || true
  fi
  TMP=$(mktemp -d)
  curl -sSfL -o "$TMP/lean.tar.zst" https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst
  unzst "$TMP/lean.tar.zst" "$TMP"
  mkdir -p "$HOME/.elan/toolchains"
  mv "$TMP/lean-4.35.0-linux" "$TC"
  rm -rf "$TMP"
fi
export PATH="$HOME/.elan/bin:$PATH"
elan default leanprover/lean4:v4.35.0 >/dev/null 2>&1 || true
lean --version

# 2. the compiled library
if [ ! -d .lake/packages/mathlib/.lake/build/lib ]; then
  want=$(cat library/lake.tar.zst.sha256)
  got=$(cat library/lake.tar.zst.part-* | sha256sum | cut -d' ' -f1)
  [ "$want" = "$got" ] || { echo "library pieces are damaged (checksum mismatch)"; exit 1; }
  cat library/lake.tar.zst.part-* | unzst - "$REPO"
fi
echo "Ready. Library restored into $REPO/.lake"
