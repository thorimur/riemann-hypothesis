import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Hilbert

namespace UpperTheory.V.Sd

structure Hypotheses4N : Prop where
  h : Af.HypothesesH
  adj : Published.AdjointLift
  cube : Published.SymCube
  ind : Published.QuadInduction
  eis : Published.HilbertEisOne
  one : Published.HilbertOne

end UpperTheory.V.Sd
