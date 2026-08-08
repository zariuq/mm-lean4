#!/bin/sh
# Permanent CLI-honesty and resource-bound gate for mm-lean4.
#
# Pins the exact accepted/verified/rejected wording of the CLI across modes
# ([MM 4.1.4]: `?` proofs are accepted with an incompleteness warning, never
# reported as verified) and the include-resolution budget canaries
# (zero / sufficient / default).  Run from the repo root:
#
#   MM_LEAN4=.lake/build/bin/mm-lean4 sh scripts/cli_honesty.sh
set -u
: "${MM_LEAN4:?MM_LEAN4 must name the freshly built mm-lean4 binary}"
fails=0
chk() { # chk <desc> <expected-exit> <grep-pattern> <args...>
  desc=$1; want=$2; pat=$3; shift 3
  out=$("$MM_LEAN4" "$@" 2>&1); got=$?
  if [ "$got" != "$want" ]; then
    echo "FAIL [$desc] exit $got != $want"; fails=$((fails+1)); return
  fi
  if ! printf '%s' "$out" | grep -q "$pat"; then
    echo "FAIL [$desc] output missing /$pat/: $out"; fails=$((fails+1)); return
  fi
  echo "ok   [$desc]"
}
neg() { # neg <desc> <forbidden-pattern> <args...>
  desc=$1; pat=$2; shift 2
  out=$("$MM_LEAN4" "$@" 2>&1)
  if printf '%s' "$out" | grep -q "$pat"; then
    echo "FAIL [$desc] output contains forbidden /$pat/: $out"; fails=$((fails+1)); return
  fi
  echo "ok   [$desc]"
}
Q=test_databases/incomplete_proofs
B=test_databases/include_budget

# [MM 4.1.4] `?` honesty
chk "zar normal ? accepted"      0 "accepted, 6 objects, 1 incomplete proof(s): incomplete" "$Q/normal_qmark.mm"
neg "zar normal ? never verified"  "verified"                                               "$Q/normal_qmark.mm"
chk "zar compressed ? accepted"  0 "accepted, 6 objects, 1 incomplete proof(s): incomplete" "$Q/compressed_qmark.mm"
neg "zar compressed ? never verified" "verified"                                            "$Q/compressed_qmark.mm"
chk "sound rejects ?"            1 "unknown step '?' not allowed"        --mode=sound "$Q/normal_qmark.mm"
chk "knife rejects ?"            1 "unknown step '?' not allowed"        --mode=knife "$Q/normal_qmark.mm"
chk "zar complete verified"      0 "verified, 6 objects"                                    "$Q/complete.mm"
chk "sound complete verified"    0 "verified, 6 objects"                 --mode=sound "$Q/complete.mm"
chk "knife complete verified"    0 "verified, 6 objects"                 --mode=knife "$Q/complete.mm"

# Include-resolution budget canaries (resource bound, not a spec violation)
chk "budget zero exhausts loudly" 1 "include resolution budget exhausted" --max-include-resolutions=0 "$B/main.mm"
chk "budget zero code 61"         1 "code #61"        --show-error-code --max-include-resolutions=0 "$B/main.mm"
chk "budget zero impl clause"     1 "impl_resourceBound" --show-error-code --max-include-resolutions=0 "$B/main.mm"
chk "budget sufficient verifies"  0 "verified, 8 objects"                --max-include-resolutions=3 "$B/main.mm"
chk "budget default verifies"     0 "verified, 8 objects"                                            "$B/main.mm"

# [MM 4.1.2] cycle semantics: a self-reference is ignored (to avoid loops).
# Canonical modes recognize a cycle and ignore it with a warning.  Literal
# mirror modes suppress only a repeated spelling; a different spelling is
# treated as a different file and normally fails later on redeclaration.
chk "zar ignores self-include"     0 "verified, 1 objects"    "$B/self_include.mm"
chk "zar warns on ignored cycle"   0 "warning: include cycle ignored" "$B/self_include.mm"
neg "sound cycle warn not fatal"     "at 1:1"                     --mode=sound "$B/self_include.mm"
chk "sound ignores self-include"   0 "verified, 1 objects"    --mode=sound "$B/self_include.mm"
# Mirror-mode include policy: literal-string file identity and
# invocation-directory lookup.  A differently-spelled self-include
# is re-included and fails on the redeclaration (as metamath.exe and
# metamath-knife do); a same-spelling one is silently skipped (as they do).
chk "knife-mode redeclares on spelled cycle" 1 "duplicate symbol" --mode=knife "$B/self_dot.mm"
chk "exe-mode redeclares on spelled cycle"   1 "duplicate symbol" --mode=exe "$B/self_dot.mm"
chk "mirror literal lookup is CWD-based"     1 "failed to read include file" --mode=exe "$B/self_include.mm"
chk "exe-mode skips same-spelling self"      0 "verified, 1 objects" --mode=exe "$B/self_lit.mm"
chk "knife-mode skips same-spelling self"    0 "verified, 1 objects" --mode=knife "$B/self_lit.mm"
neg "mirror skip is silent"                    "warning"             --mode=exe "$B/self_lit.mm"

if [ "$fails" != 0 ]; then echo "$fails failure(s)"; exit 1; fi
echo "all CLI honesty gates green"
