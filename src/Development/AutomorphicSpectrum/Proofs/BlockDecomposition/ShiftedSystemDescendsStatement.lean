import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescends
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι), A.Desc → (shSy ς k A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | exact GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.ShDesc.sh_desc <;> assumption)
