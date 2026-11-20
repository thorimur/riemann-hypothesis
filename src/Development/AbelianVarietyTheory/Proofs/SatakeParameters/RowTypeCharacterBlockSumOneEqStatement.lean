import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTypeCharacterBlockSumOneEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2 GlobalTheory.TopStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTypeCharacter_blockSumOne_eq : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {N n : ℕ} (hN : N = n + 1) (r : ℕ), r ≤ n → ∀ j : Sp E n ≃ₗ[E] Sp E n, LocE.lamQB ξ r N (sumE hN j 1).toLinearMap = LocE.lamQB ξ r n j.toLinearMap := by
  first | exact @GlobalTheory.SumRowType.lamQB_sumE | exact GlobalTheory.SumRowType.lamQB_sumE | (intros; apply GlobalTheory.SumRowType.lamQB_sumE <;> assumption)
