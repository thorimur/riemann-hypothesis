import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toZ_isArithHeight_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (h : X → ℝ), (toZ L t hL).IsArithHeight h ↔ L.IsArithHeight h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff | exact GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.isArithHeight_toZ_iff <;> assumption)
