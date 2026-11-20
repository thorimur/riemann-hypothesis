import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison.Pb

theorem vb_fin : ∀ {O : Type} [CommRing O] [IsNoetherianRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : (⨆ α, U α) = ⊤) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (K : Cos.{1} O) (V : VB (fun W => ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ W le_top).hom) U K) (p : ℕ),
    Module.Finite O (K.cx.H p) := @GlobalTheory.CompanionTheory.VBGlue.finite_H_cx

theorem serre_fg : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∃ 𝒮 : Serre.{1} R,
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ Module.Finite R M := @GlobalTheory.T.finite_modules_serre_class

end CrystallineSemistableComparison.Pb
