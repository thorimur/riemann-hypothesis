import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_right_haar_measure : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ μ : Measure (GA E a), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant | exact GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant | (intros; apply GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant <;> assumption)
