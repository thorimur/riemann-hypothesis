import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectSumSystemDescends
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.direct_sum_system_descends : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I] (A : I → Sy.{1} K ι), (∀ i, (A i).Desc) → (sumSy A).Desc := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | exact GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc | (intros; apply GlobalTheory.CompanionTheory.KunGlue.SumDesc.sum_desc <;> assumption)
