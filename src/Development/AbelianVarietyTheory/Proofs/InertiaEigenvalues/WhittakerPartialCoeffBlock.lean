import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableHopfOrderSubgroupTranslation
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_partial_coeff_block : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → ∀ h : GA E (m + 1),
    GlobalTheory.JSW.whit (fun h => partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) h =
      GlobalTheory.JSW.whit φ (blockGL (by omega : m + 1 ≤ k + 1) h) := by
  first | (exact @GlobalTheory.RSnm.whit_partialCoeff_comp_blockGL) | (exact GlobalTheory.RSnm.whit_partialCoeff_comp_blockGL) | (intros; apply GlobalTheory.RSnm.whit_partialCoeff_comp_blockGL  <;> assumption)
