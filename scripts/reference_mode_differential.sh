#!/usr/bin/env bash
# Compare each mirror mode's acceptance verdict with its reference executable
# on every database registered by metamath-test/run-testsuite-all.

set -u

: "${MM_LEAN4:?MM_LEAN4 must name the freshly built mm-lean4 executable}"
: "${METAMATH_KNIFE:?METAMATH_KNIFE must name the metamath-knife executable}"
: "${METAMATH_EXE:?METAMATH_EXE must name the metamath.exe executable}"
: "${METAMATH_TEST:?METAMATH_TEST must name the metamath-test directory}"

for executable in "$MM_LEAN4" "$METAMATH_KNIFE" "$METAMATH_EXE"; do
  if [[ ! -x "$executable" ]]; then
    echo "not executable: $executable" >&2
    exit 2
  fi
done

suite="$METAMATH_TEST/run-testsuite-all"
tests_root="$METAMATH_TEST/tests"
if [[ ! -f "$suite" || ! -d "$tests_root" ]]; then
  echo "METAMATH_TEST does not contain run-testsuite-all and tests/" >&2
  exit 2
fi

mapfile -t databases < <(
  awk '$1 == "pass" || $1 == "fail" { gsub(/\\/, "", $2); print $2 }' "$suite"
)
if [[ ${#databases[@]} -eq 0 ]]; then
  echo "no registered databases found in $suite" >&2
  exit 2
fi

mm_verdict() {
  local mode=$1 directory=$2 basename=$3
  (cd "$directory" && timeout 300 "$MM_LEAN4" --mode="$mode" "$basename" >/dev/null 2>&1)
  local status=$?
  case $status in
    0) printf 'accept' ;;
    1) printf 'reject' ;;
    *) printf 'harness-error:%s' "$status" ;;
  esac
}

knife_verdict() {
  local directory=$1 basename=$2
  (cd "$directory" &&
    timeout 300 "$METAMATH_KNIFE" --verify --split --jobs 4 "$basename" >/dev/null 2>&1)
  local status=$?
  case $status in
    0) printf 'accept' ;;
    1) printf 'reject' ;;
    *) printf 'harness-error:%s' "$status" ;;
  esac
}

exe_verdict() {
  local directory=$1 basename=$2 output
  output=$(cd "$directory" &&
    timeout 300 "$METAMATH_EXE" "read \"$basename\"" 'verify proof *' exit 2>&1)
  local status=$?
  # Metamath.exe reports ordinary read and verification failures in its output
  # while returning zero. Any nonzero process status is therefore an execution
  # failure, not a semantic verdict.
  if [[ $status -ne 0 ]]; then
    printf 'harness-error:%s' "$status"
    return
  fi
  # metamath.exe normally exits zero even after a read or verification error.
  # Warnings, including accepted incomplete proofs, are not rejection.  These
  # are the stable fatal contours emitted by its reader and verifier.
  if grep -Eq '^\?Error|^\?End of comment not found|[1-9][0-9]* errors? (was|were) found' <<<"$output"; then
    printf 'reject'
  else
    printf 'accept'
  fi
}

failures=0
harness_failures=0
knife_checked=0
exe_checked=0
total=${#databases[@]}

for relative in "${databases[@]}"; do
  file="$tests_root/$relative"
  if [[ ! -f "$file" ]]; then
    echo "missing registered database: $relative" >&2
    failures=$((failures + 1))
    continue
  fi
  directory=$(dirname "$file")
  basename=$(basename "$file")

  ours=$(mm_verdict knife "$directory" "$basename")
  reference=$(knife_verdict "$directory" "$basename")
  if [[ "$ours" == harness-error:* || "$reference" == harness-error:* ]]; then
    echo "knife harness failure: $relative (mm-lean4=$ours, reference=$reference)" >&2
    harness_failures=$((harness_failures + 1))
  else
    knife_checked=$((knife_checked + 1))
    if [[ "$ours" != "$reference" ]]; then
      echo "knife mismatch: $relative (mm-lean4=$ours, reference=$reference)" >&2
      failures=$((failures + 1))
    fi
  fi

  ours=$(mm_verdict exe "$directory" "$basename")
  reference=$(exe_verdict "$directory" "$basename")
  if [[ "$ours" == harness-error:* || "$reference" == harness-error:* ]]; then
    echo "exe harness failure: $relative (mm-lean4=$ours, reference=$reference)" >&2
    harness_failures=$((harness_failures + 1))
  else
    exe_checked=$((exe_checked + 1))
    if [[ "$ours" != "$reference" ]]; then
      echo "exe mismatch: $relative (mm-lean4=$ours, reference=$reference)" >&2
      failures=$((failures + 1))
    fi
  fi
done

echo "knife mirror: $knife_checked/$total semantic verdicts compared"
echo "exe mirror:   $exe_checked/$total semantic verdicts compared"

if [[ $harness_failures -ne 0 ]]; then
  echo "reference differential: $harness_failures harness failure(s)" >&2
  exit 2
fi

if [[ $failures -ne 0 ]]; then
  echo "reference differential: $failures mismatch(es)" >&2
  exit 1
fi

echo "reference differential: exact acceptance agreement"
