import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetCapelliOperator
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_capelli_operator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : E →+* ℂ) (u : ℂ) (φ : π.V), (Formalism.REAL.qdet (EopV π τ) (u + ((a : ℂ) - 1) / 2) φ).1 = cap τ u φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val | exact GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val | (intros; apply GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val <;> assumption)
