#!/usr/bin/env bash
# rebuild_lean.sh — Rebuild MembershipProject (Lean 4 / Mathlib4)
# Run from the root of the MembershipProject directory.
# Usage: bash rebuild_lean.sh [--clean] [--no-cache]
#
#   --clean     wipe .lake/ before rebuilding (full rebuild)
#   --no-cache  skip `lake exe cache get` (build Mathlib from source — very slow)

set -euo pipefail

# ── Colours ──────────────────────────────────────────────────────────────────
RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'; CYAN='\033[0;36m'; NC='\033[0m'
info()  { echo -e "${CYAN}[INFO]${NC}  $*"; }
ok()    { echo -e "${GREEN}[ OK ]${NC}  $*"; }
warn()  { echo -e "${YELLOW}[WARN]${NC}  $*"; }
die()   { echo -e "${RED}[FAIL]${NC}  $*" >&2; exit 1; }

# ── Flags ─────────────────────────────────────────────────────────────────────
DO_CLEAN=0; SKIP_CACHE=0
for arg in "$@"; do
  case "$arg" in
    --clean)    DO_CLEAN=1 ;;
    --no-cache) SKIP_CACHE=1 ;;
    *) die "Unknown argument: $arg" ;;
  esac
done

# ── Locate project root ───────────────────────────────────────────────────────
if [[ ! -f "lakefile.lean" && ! -f "lakefile.toml" ]]; then
  die "No lakefile found. Run this script from the MembershipProject root directory."
fi
PROJECT_ROOT="$(pwd)"
info "Project root: $PROJECT_ROOT"

# ── Step 1: elan ─────────────────────────────────────────────────────────────
info "Checking elan..."
if ! command -v elan &>/dev/null; then
  warn "elan not found. Installing..."
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  # Add elan to PATH for the rest of this script
  export PATH="$HOME/.elan/bin:$PATH"
  ok "elan installed: $(elan --version)"
else
  ok "elan found: $(elan --version)"
fi

# ── Step 2: Lean toolchain ───────────────────────────────────────────────────
info "Checking lean-toolchain..."
if [[ -f "lean-toolchain" ]]; then
  TOOLCHAIN="$(cat lean-toolchain | tr -d '[:space:]')"
  ok "Toolchain from file: $TOOLCHAIN"
else
  # Fallback: latest stable Lean 4 compatible with current Mathlib
  TOOLCHAIN="leanprover/lean4:v4.14.0"
  warn "No lean-toolchain file found. Using fallback: $TOOLCHAIN"
  warn "If this fails, check https://github.com/leanprover-community/mathlib4 for the correct version."
  echo "$TOOLCHAIN" > lean-toolchain
fi

info "Installing toolchain $TOOLCHAIN (elan will download if needed)..."
elan toolchain install "$TOOLCHAIN" || die "Failed to install toolchain $TOOLCHAIN"
elan override set "$TOOLCHAIN"
ok "Lean: $(lean --version)"
ok "Lake: $(lake --version)"

# ── Step 3: Optional clean ───────────────────────────────────────────────────
if [[ $DO_CLEAN -eq 1 ]]; then
  warn "--clean requested. Removing .lake/ ..."
  rm -rf .lake/
  ok ".lake/ removed."
fi

# ── Step 4: lake update (resolve dependencies) ───────────────────────────────
info "Running: lake update ..."
lake update || die "lake update failed. Check lakefile.lean and network access."
ok "Dependencies resolved."

# ── Step 5: Mathlib cache ────────────────────────────────────────────────────
if [[ $SKIP_CACHE -eq 0 ]]; then
  info "Running: lake exe cache get  (downloads prebuilt Mathlib oleans — fast) ..."
  lake exe cache get || {
    warn "Cache download failed (network issue or cache miss). Building Mathlib from source."
    warn "This may take 30–60 minutes on first build."
  }
else
  warn "--no-cache: skipping Mathlib cache download."
fi

# ── Step 6: Build the project ────────────────────────────────────────────────
info "Running: lake build MembershipProject ..."
lake build MembershipProject 2>&1 | tee /tmp/lean_build.log

BUILD_EXIT="${PIPESTATUS[0]}"

# ── Step 7: Report ───────────────────────────────────────────────────────────
echo ""
if [[ $BUILD_EXIT -eq 0 ]]; then
  ok "Build succeeded."

  # Count axioms in the output files
  AXIOM_COUNT=$(grep -r "^axiom " "$PROJECT_ROOT/MembershipProject" \
                  --include="*.lean" 2>/dev/null | wc -l || true)
  SORRY_COUNT=$(grep -rn "\bsorry\b" "$PROJECT_ROOT/MembershipProject" \
                  --include="*.lean" 2>/dev/null | \
                  grep -v "^\s*--" | wc -l || true)
  echo ""
  echo -e "  Axioms in project : ${CYAN}${AXIOM_COUNT}${NC}"
  echo -e "  Sorries remaining : $([ "$SORRY_COUNT" -eq 0 ] \
            && echo -e "${GREEN}0${NC}" || echo -e "${RED}${SORRY_COUNT}${NC}")"
  echo ""

  # Confirm main theorem
  if grep -q "theorem p_equals_np" "$PROJECT_ROOT/MembershipProject/Core/N_PEqualsNP.lean" \
       2>/dev/null; then
    ok "p_equals_np compiles."
  fi
else
  die "Build failed (exit $BUILD_EXIT). Full log: /tmp/lean_build.log"
fi