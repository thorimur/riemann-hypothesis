import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_operator_eigenvalue_sum : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ φ ∈ π.V, (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := by
  first | exact @GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq | exact GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq | (intros; apply GlobalTheory.CompanionTheory.CapelliTrace.trace_Eop_eq <;> assumption)
