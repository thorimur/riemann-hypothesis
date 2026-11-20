import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitTranslateBoundedOfFactors
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unit_translate_bounded_of_factors : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.ProductUnitBounded := by
  first | exact @GlobalTheory.RegSS.productUnitBounded | exact GlobalTheory.RegSS.productUnitBounded | (intros; apply GlobalTheory.RegSS.productUnitBounded <;> assumption)
