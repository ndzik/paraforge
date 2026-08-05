#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
build_dir=$(mktemp -d "${TMPDIR:-/tmp}/paraforge-nca-json.XXXXXX")
trap 'rm -rf "$build_dir"' EXIT

cat >"$build_dir/RenderNCA.agda" <<'AGDA'
{-# OPTIONS --guardedness #-}

module RenderNCA where

open import IO.Base using (Main; run)
open import IO.Finite using (putStr)
open import ParaForge.Examples.ExportNCA using (ncaJSON)

main : Main
main = run (putStr ncaJSON)
AGDA

agda --compile \
  --compile-dir="$build_dir/compiled" \
  -i "$root/src" \
  -i "$build_dir" \
  -l standard-library-2.4 \
  -l agda-categories \
  "$build_dir/RenderNCA.agda" >/dev/null

"$build_dir/compiled/RenderNCA"
