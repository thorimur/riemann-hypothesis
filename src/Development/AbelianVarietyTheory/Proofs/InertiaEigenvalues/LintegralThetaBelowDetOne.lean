import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieModelFiniteBaseChange
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_below_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π' : CuspSub E (m + 1)), π'.IsUnitary →
    ∀ φ' ∈ GlobalTheory.JSW.mspanR π', ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕 : Set (GA E (m + 1))),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → ∀ x : ℝ, 1 < x →
      ∫⁻ g in 𝓕 ∩ {g | GlobalTheory.RSnm.detAbs g ≤ 1}, ‖φ' g‖ₑ ^ 2 * (∑' ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0}, ‖G (Matrix.vecMul (fun j => algebraMap E (Ad E) (ξ.1 j)) g.val)‖ₑ) * ENNReal.ofReal (GlobalTheory.RSnm.detAbs g ^ x) ∂μ ≠ ⊤ := by
  first | (exact @GlobalTheory.ThetaSqLow.lintegral_low_ne_top) | (exact GlobalTheory.ThetaSqLow.lintegral_low_ne_top) | (intros; apply GlobalTheory.ThetaSqLow.lintegral_low_ne_top  <;> assumption)
