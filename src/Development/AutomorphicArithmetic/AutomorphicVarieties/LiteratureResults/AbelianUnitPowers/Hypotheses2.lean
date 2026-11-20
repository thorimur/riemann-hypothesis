import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

namespace UpperTheory.V.Sd

structure HypothesesL : Prop where
  af : Af.Hypotheses₂
  eg : PropEG
  adj : Lit.AdAutQ
  bc : Z.Bc.LiftC

end UpperTheory.V.Sd
