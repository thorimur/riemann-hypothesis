import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundPrimedOfUnprimed
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantLengthTailBound_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  first | exact @GlobalTheory.TypeAsm.tailBd_primed_of_unprimed | exact GlobalTheory.TypeAsm.tailBd_primed_of_unprimed | (intros; apply GlobalTheory.TypeAsm.tailBd_primed_of_unprimed <;> assumption)
