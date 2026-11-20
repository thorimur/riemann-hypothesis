import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.OneUseOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym

namespace UpperTheory.V.Sd

structure MixedUnitPublishedTheorems : Prop where
  h : Af.HypothesesH
  adj : Lit.AdAutQ
  ind : Published.QuadInduction
  eis : Published.HilbertEisOne
  one : Lit.OneUse

end UpperTheory.V.Sd
