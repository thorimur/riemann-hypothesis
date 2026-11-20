import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictSelfPullCEq
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrict_self_pullC_eq : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n), (resU F k).pullC n x = x := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC | exact GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC | (intros; apply GlobalTheory.CompanionTheory.KunGlue.resU_self_pullC <;> assumption)
