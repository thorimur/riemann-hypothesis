import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtalePolynomialPlaceToPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyEtale_polynomialPlace_to_place : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K)
    (T : Subring L) (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK)
    (j : K →+* L), IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
    (∀ g : R, j (g : K) = (ι g : L)) → ∀ (hA : ∀ f ∈ P0.ring, j f ∈ P.ring)
    (hτ : ∀ i, (τ i : L) ∈ P.ring),
    (MvPolynomial.eval₂Hom (j.restrict P0.ring P.ring hA) (fun i => (⟨τ i, hτ i⟩ : P.ring))).FormallyEtale := by
  first | exact @GlobalTheory.FieldPair.formallyEtale_polyPlace | exact GlobalTheory.FieldPair.formallyEtale_polyPlace | (intros; apply GlobalTheory.FieldPair.formallyEtale_polyPlace <;> assumption)
