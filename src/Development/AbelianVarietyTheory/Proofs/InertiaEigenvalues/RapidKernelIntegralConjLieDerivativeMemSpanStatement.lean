import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidKernelIntegralConjLieDerivativeMemSpan
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapidKernel_integral_conjLieDerivative_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (Y : Lie E a), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν) ∈ GlobalTheory.MSpanDecay.kSpan E a := by
  first | exact @GlobalTheory.MSpanDecay.integral_lieD_conj_mem_kSpan | exact GlobalTheory.MSpanDecay.integral_lieD_conj_mem_kSpan | (intros; apply GlobalTheory.MSpanDecay.integral_lieD_conj_mem_kSpan <;> assumption)
