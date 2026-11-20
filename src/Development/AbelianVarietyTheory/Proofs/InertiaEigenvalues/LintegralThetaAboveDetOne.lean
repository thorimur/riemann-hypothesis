import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerMapFlatSemiabelian
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_above_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ,
      ∫⁻ g in 𝓕 ∩ {g | 1 ≤ GlobalTheory.RSnm.detAbs g}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  first | (exact @GlobalTheory.SBThetaUpper.lintegral_theta_upper_ne_top) | (exact GlobalTheory.SBThetaUpper.lintegral_theta_upper_ne_top) | (intros; apply GlobalTheory.SBThetaUpper.lintegral_theta_upper_ne_top  <;> assumption)
