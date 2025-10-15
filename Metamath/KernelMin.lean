import Metamath.Spec
import Metamath.Verify
import Metamath.KernelExtras

namespace Metamath.Kernel

open Metamath.Spec
open Metamath.Verify

def toSym (s : Metamath.Verify.Sym) : Metamath.Spec.Sym := s.value

def toExpr (f : Metamath.Verify.Formula) : Metamath.Spec.Expr :=
  if h : f.size > 0 then
    { typecode := ⟨f[0].value⟩, syms := f.toList.tail.map toSym }
  else
    { typecode := ⟨"ERROR"⟩, syms := [] }

axiom toDatabase (db : Metamath.Verify.DB) : Option Metamath.Spec.Database
axiom toFrame (db : Metamath.Verify.DB) (fr : Metamath.Verify.Frame) : Option Metamath.Spec.Frame

theorem verify_impl_sound
    (db : Metamath.Verify.DB)
    (f : Metamath.Verify.Formula) :
  ∃ (Γ : Metamath.Spec.Database) (fr : Metamath.Spec.Frame),
    toDatabase db = some Γ ∧
    toFrame db db.frame = some fr ∧
    Metamath.Spec.Provable Γ fr (toExpr f) := by
  sorry

end Metamath.Kernel
