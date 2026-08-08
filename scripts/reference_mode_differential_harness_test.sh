#!/usr/bin/env bash
# Canary tests for rejection versus reference-process failure classification.

set -eu

root=$(mktemp -d)
trap 'rm -rf "$root"' EXIT
mkdir -p "$root/bin" "$root/corpus/tests/unit"
printf 'pass unit/sample.mm\n' >"$root/corpus/run-testsuite-all"
printf '%s\n' "\$c wff \$." >"$root/corpus/tests/unit/sample.mm"

make_mock() {
  local path=$1 body=$2
  printf '#!/usr/bin/env bash\n%s\n' "$body" >"$path"
  chmod +x "$path"
}

make_mock "$root/bin/mm" 'exit 0'
make_mock "$root/bin/knife" 'exit 0'
make_mock "$root/bin/exe" 'exit 0'

run_gate() {
  MM_LEAN4="$root/bin/mm" \
  METAMATH_KNIFE="$root/bin/knife" \
  METAMATH_EXE="$root/bin/exe" \
  METAMATH_TEST="$root/corpus" \
    "$(dirname "$0")/reference_mode_differential.sh" >/dev/null 2>&1
}

run_gate

make_mock "$root/bin/exe" 'printf "?Error: rejected\n"; exit 0'
if run_gate; then
  echo 'fatal: a semantic rejection was classified as acceptance' >&2
  exit 1
fi

make_mock "$root/bin/exe" 'exit 7'
set +e
run_gate
status=$?
set -e
if [[ $status -ne 2 ]]; then
  echo "fatal: reference execution failure returned $status instead of 2" >&2
  exit 1
fi

make_mock "$root/bin/exe" 'exit 0'
make_mock "$root/bin/knife" 'exit 101'
set +e
run_gate
status=$?
set -e
if [[ $status -ne 2 ]]; then
  echo "fatal: knife process failure returned $status instead of 2" >&2
  exit 1
fi

echo 'reference differential harness canaries: pass'
