#!/usr/bin/env bash
# A bounded, logged invocation of the unchanged research functions.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $# -lt 2 || $# -gt 4 ]]; then
  echo "Usage: bash scripts/reproduce-h2.sh CASE PRIME [SECONDS=5, maximum 30] [standard|large]" >&2
  exit 2
fi
research_case=$1
research_prime=$2
research_seconds=${3:-5}
research_mode=${4:-standard}
case "$research_case" in
  SL2F2|SL2F3|SL2F5) ;;
  *) echo "Full H2 runs are deferred outside the small finite-group whitelist; use benchmarks/run.py --task abelian or construction" >&2; exit 2 ;;
esac
[[ $research_prime =~ ^[1-9][0-9]*$ && $research_seconds =~ ^[1-9][0-9]*$ ]] || {
  echo "PRIME and SECONDS must be positive integers" >&2; exit 2;
}
[[ $research_seconds =~ ^([1-9]|[12][0-9]|30)$ ]] || {
  echo "Quick-baseline runs are capped at 30 seconds" >&2; exit 2;
}
case "$research_mode" in
  standard) research_large=false ;;
  large) research_large=true ;;
  *) echo "Mode must be standard or large" >&2; exit 2 ;;
esac
research_gap=${GAP_BIN:-gap}
research_log=$(mktemp -d "${TMPDIR:-/tmp}/group-homology.XXXXXXXX")
echo "Run artifacts: $research_log"
{
  git rev-parse HEAD
  git hash-object Algorithms.g Library-of-groups.g
  git status --short
  printf 'case=%s prime=%s seconds=%s mode=%s\n' "$research_case" "$research_prime" "$research_seconds" "$research_mode"
  date -u +%FT%TZ
} > "$research_log/metadata.txt"
research_time=${TIME_BIN:-/usr/bin/time}
research_timer=()
if [[ -x $research_time ]]; then
  research_timer=("$research_time" -f 'wall_seconds=%e\npeak_rss_kib=%M' -o "$research_log/resources.txt")
fi
research_started=$SECONDS
set +e
"${research_timer[@]}" \
  timeout --kill-after=5s "${research_seconds}s" "$research_gap" -q -b --quitonbreak \
  -c "ResearchCase := \"$research_case\";; ResearchPrime := $research_prime;; ResearchLarge := $research_large;;" \
  tests/reproduce-h2.g 2>&1 | tee "$research_log/output.log"
research_status=${PIPESTATUS[0]}
set -e
if [[ ${#research_timer[@]} -eq 0 ]]; then
  printf 'wall_seconds_approx=%s\npeak_rss_kib=unavailable (GNU time not installed)\n' \
    "$((SECONDS - research_started))" > "$research_log/resources.txt"
fi
printf '%s\n' "$research_status" > "$research_log/exit-status.txt"
echo "Exit status: $research_status (124 indicates timeout; see artifacts for details)"
exit "$research_status"
