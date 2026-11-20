import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.NewtonThorneSym
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert

namespace UpperTheory.V.Sd

structure Hypotheses4L : Prop where
  h : Af.HypothesesH
  adj : Lit.AdAutQ
  cube : Lit.SymmetricCubeAutomorphyOverRationals
  ind : Published.QuadInduction
  eis : Published.HilbertEisOne
  one : Published.HilbertOne

end UpperTheory.V.Sd
