import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScaling
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_borel_section_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (a : GlobalTheory.CompanionTheory.Ar.Rec.WZ E) (f : Rul Xo c) (L : Type) [Field L] [Algebra c.F L] (t : Ix Dw → Lˣ) (y y' : FrPt Xo c L), f ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a → FrBor t y y' → evR Xo c f y' = ((∏ i, t i ^ GlobalTheory.CompanionTheory.Ar.Rec.exZ Dw a i : Lˣ) : L) * evR Xo c f y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field | exact GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field <;> assumption)
