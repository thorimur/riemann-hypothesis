import Development.WeilBound.CoreStatements.HodgeTatePoints.PpicDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.polarized_abelian_part_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), GlobalTheory.LN.CDvr V → Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → GlobalTheory.LN.PolAt tV (Out.jK V) → ∀ P : AbPart tV (spMap r), IsPrincipal P.tB := by
  first | exact @PositivityTheory.HtPt.Ppic.dvr | exact PositivityTheory.HtPt.Ppic.dvr
