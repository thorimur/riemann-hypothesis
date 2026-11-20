import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfMonomialQuotientIntegral
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.root_of_monomial_quotient_integral : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (P : Ideal A) [P.IsPrime] (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (S : Finset (Fin n)) (g : L) (m : ℕ), 0 < m → (∃ a b : A, b ∉ P ∧ g ^ m / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a) → ∃ a b : A, b ∉ P ∧ g / algebraMap A L (∏ j ∈ S, t j) * algebraMap A L b = algebraMap A L a := by
  first | exact @_root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow | exact _root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow | (intros; apply _root_.GlobalTheory.EtRoot.div_prod_coords_mem_of_pow <;> assumption)
