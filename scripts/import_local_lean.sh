#!/usr/bin/env bash
# Import the current locally verified Lean project without modifying the source.
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
SOURCE="${ERDOS_MAHLER_LEAN_SOURCE:-$HOME/Desktop/Auditoria ERDOSMAHLER/lean4/ErdosMahlerAudit}"
DEST="$ROOT/formalization/ErdosMahlerAudit"

fail() {
  printf 'ERROR: %s\n' "$*" >&2
  exit 1
}

test -d "$SOURCE" || fail "Local Lean project not found: $SOURCE"
test -d "$ROOT/.git" || fail "Run from a clone of the repository."
test "$(git -C "$ROOT" branch --show-current)" = main || fail "Expected the main branch."
test -z "$(git -C "$ROOT" status --porcelain)" || fail "Commit or stash unrelated local changes before importing."

remote="$(git -C "$ROOT" remote get-url origin)"
case "$remote" in
  https://github.com/DiegoMarquesMath/Erdos-Mahler|https://github.com/DiegoMarquesMath/Erdos-Mahler.git|git@github.com:DiegoMarquesMath/Erdos-Mahler.git)
    ;;
  *)
    fail "Unexpected origin remote: $remote"
    ;;
esac

for f in lean-toolchain lakefile.toml lake-manifest.json ErdosMahlerAudit.lean \
         ErdosMahlerAudit/Gate01Checks.lean \
         ErdosMahlerAudit/Gate02Checks.lean \
         ErdosMahlerAudit/Gate03Checks.lean \
         source/Erdos_Mahler.tex source/Erdos_Mahler.pdf; do
  test -s "$SOURCE/$f" || fail "Missing required source file: $f"
done

verify_sha256() {
  local expected="$1" filepath="$2" actual
  actual="$(shasum -a 256 "$filepath" | awk '{print $1}')"
  test "$expected" = "$actual" || fail "Frozen manuscript hash mismatch: $filepath"
}

verify_sha256 \
  5a55f32babc285ed9ad05fcb3bd6f8fe2bd3080d9eca7fd11e79ba23f7307116 \
  "$SOURCE/source/Erdos_Mahler.tex"
verify_sha256 \
  9d9558f33236b6c1d7b276876153bf3d87f6fac2019c6e39db4d988e5022927f \
  "$SOURCE/source/Erdos_Mahler.pdf"

printf 'Verifying local Lean build before publication...\n'
(cd "$SOURCE" && lake build)

mkdir -p "$DEST/ErdosMahlerAudit" "$DEST/source"

# Copy only the necessary Lean sources and pinned project manifests.
cp "$SOURCE/lean-toolchain" "$SOURCE/lakefile.toml" "$SOURCE/lake-manifest.json" "$DEST/"
find "$SOURCE" -maxdepth 1 -name '*.lean' -type f -exec cp {} "$DEST/" \;
rsync -a --prune-empty-dirs \
  --include='*/' --include='*.lean' --exclude='*' \
  "$SOURCE/ErdosMahlerAudit/" "$DEST/ErdosMahlerAudit/"

cp "$SOURCE/source/Erdos_Mahler.tex" "$SOURCE/source/Erdos_Mahler.pdf" "$DEST/source/"

# No journal-specific material or local audit instructions are transferred.
forbidden="$(printf '%b' '\\141\\156\\156\\141\\154\\163')"
if grep -RinEi --exclude='*.pdf' --exclude-dir=.git --exclude='*.zip' \
  "$forbidden" "$ROOT/README.md" "$ROOT/FORMALIZATION_STATUS.md" "$ROOT/CITATION.cff" \
  "$ROOT/docs" "$ROOT/scripts" "$ROOT/.github" "$DEST"; then
  fail "Disallowed journal reference found in publication files; source unchanged."
fi

printf 'Files prepared for the remote verification build:\n'
git -C "$ROOT" status --short

git -C "$ROOT" add -A formalization/ErdosMahlerAudit
if git -C "$ROOT" diff --cached --quiet; then
  printf 'No new changes to commit.\n'
  exit 0
fi

git -C "$ROOT" commit -m "formalization: import current locally checked Lean sources with pinned dependencies"
git -C "$ROOT" push origin main

printf 'Lean source published. Check the GitHub Actions workflow for independent build results.\n'
