import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChange
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_finite_generation_of_affine_base_change : ∀ (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1) (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) → CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  first | exact @GlobalTheory.CechTr.cechFG_of_baseChange_affine | exact GlobalTheory.CechTr.cechFG_of_baseChange_affine | (intros; apply GlobalTheory.CechTr.cechFG_of_baseChange_affine <;> assumption)
