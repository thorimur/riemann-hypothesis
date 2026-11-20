import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmEllipticCurve_isPureHodgeEndomorphismBaseChange : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω), IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  first | exact @GlobalTheory.PureLift.isPureBC_ell | exact GlobalTheory.PureLift.isPureBC_ell | (intros; apply GlobalTheory.PureLift.isPureBC_ell <;> assumption)
