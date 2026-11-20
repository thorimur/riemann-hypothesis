import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageQuotientFibre
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_quotientFibre : ∀ (X Z : Scheme.{0}) (p : Z ⟶ X) (U : X.affineOpens) (m : Ideal Γ(X, U.1)) (A : Scheme.{0}) (q : A ⟶ Sp (Γ(X, U.1) ⧸ m)) (ι : A ⟶ Z), IsPullback ι q p (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ W : Z.Opens, IsAffineOpen W → W ≤ p ⁻¹ᵁ U.1 → IsAffineOpen (ι ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | exact GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre | (intros; apply GlobalTheory.AffinePreimageFibre.isAffineOpen_preimage_fibre <;> assumption)
