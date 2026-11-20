import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_cohomology_finite : ∀ {O : Type} [CommRing O] [IsNoetherianRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : (⨆ α, U α) = ⊤) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (K : Cos.{1} O) (V : VB (fun W => ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ W le_top).hom) U K) (p : ℕ),
    Module.Finite O (K.cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.VBGlue.finite_H_cx | exact GlobalTheory.CompanionTheory.VBGlue.finite_H_cx | (intros; apply GlobalTheory.CompanionTheory.VBGlue.finite_H_cx <;> assumption)
