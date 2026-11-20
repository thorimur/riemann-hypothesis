import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DetLatticeLineBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_lattice_line_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat | exact GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat <;> assumption)
