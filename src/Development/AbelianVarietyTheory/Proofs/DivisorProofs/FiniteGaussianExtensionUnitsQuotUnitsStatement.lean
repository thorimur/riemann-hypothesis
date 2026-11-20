import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGaussianExtensionUnitsQuotUnits
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_gaussianExtension_units_quot_units : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) := by
  first | exact @GlobalTheory.GaussExt.finite_units_quot_units | exact GlobalTheory.GaussExt.finite_units_quot_units | (intros; apply GlobalTheory.GaussExt.finite_units_quot_units <;> assumption)
