import Metamath.DeclarativeSpec

/-! Re-exports Mario Carneiro's declarative Metamath spec into `Spec.Semantic`.
See `DeclarativeSpec.lean` for definitions. -/

namespace Metamath.Spec.Semantic

export Metamath (CN VR Sym Expr Formula DJ Context Statement Provable)

end Metamath.Spec.Semantic
