import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_central_element_trace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  first | exact @GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop | exact GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop | (intros; apply GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop <;> assumption)
