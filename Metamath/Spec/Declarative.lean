import Metamath.DeclarativeSpec

/-! Re-exports the declarative Metamath specification of `DeclarativeSpec.lean` (Mario Carneiro's,
with the `ax` typing premise restricted to the applied statement's variables) into `Spec.Declarative`. -/

namespace Metamath.Spec.Declarative

export Metamath (CN VR Sym Expr Formula DJ Context Statement Provable)

end Metamath.Spec.Declarative
