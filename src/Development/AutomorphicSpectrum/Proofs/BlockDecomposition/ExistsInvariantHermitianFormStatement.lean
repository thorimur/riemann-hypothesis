import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_hermitian_form : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  first | exact @GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm | exact GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm | (intros; apply GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm <;> assumption)
