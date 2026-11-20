import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperator
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowth_rapidKernelOperator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Growth F → GlobalTheory.MSpanDecay.Growth (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  first | exact @GlobalTheory.MSpanDecay.growth_kernel | exact GlobalTheory.MSpanDecay.growth_kernel | (intros; apply GlobalTheory.MSpanDecay.growth_kernel <;> assumption)
