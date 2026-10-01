import Metamath.Verify

/-!
# Cross-scope floating-hypothesis types

Every mode permits a variable to be redeclared with a different type after its
previous scope closes. Assertion frames retain their own floating hypotheses;
applying an assertion still requires the corresponding type at each premise.
These executable regressions distinguish that policy from proof acceptance.
-/

namespace Metamath.TypePolicyCalibration

open Metamath.Verify

def modes : List ModeConfig :=
  [ModeConfig.zar, ModeConfig.sound, ModeConfig.knife, ModeConfig.exe, ModeConfig.permissive]

def firstScope : String :=
  "$c wff class $. ${ $v x $. wx $f wff x $. ax $a wff x $. " ++
  "first $p wff x $= wx ax $. $} "

def laterScope (tc proof : String) : ByteArray :=
  (firstScope ++ "${ $v x $. fx $f " ++ tc ++ " x $. " ++
    "second $p " ++ tc ++ " x $= " ++ proof ++ " $. $}").toUTF8

-- A later declaration with either the same or a different type is permitted.
#guard modes.all fun config =>
  (checkBytes (laterScope "wff" "fx ax") config).error?.isNone
#guard modes.all fun config =>
  let db := checkBytes (laterScope "class" "fx") config
  db.error?.isNone && db.incompleteProofs.isEmpty &&
    (db.find? "first").isSome && (db.find? "second").isSome

-- Retyping cannot change the old assertion's required `wff` premise into `class`.
#guard modes.all fun config =>
  (checkBytes (laterScope "class" "fx ax") config).error?.isSome

-- The earlier scope's floating label is not active in the later proof.
#guard modes.all fun config =>
  (checkBytes (laterScope "class" "wx") config).error?.isSome

end Metamath.TypePolicyCalibration
