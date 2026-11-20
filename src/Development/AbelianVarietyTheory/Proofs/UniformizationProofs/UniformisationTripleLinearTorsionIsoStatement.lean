import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTripleLinearTorsionIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_triple_linear_torsionIso : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : Unif I D A t.G), U.LG = t.PP → ∃ P : PELUnif I t, P.D = D ∧ P.A = A ∧ HEq P.U U ∧ P.TorsionIso := by
  first | exact @GlobalTheory.PELOfUnif.main | exact GlobalTheory.PELOfUnif.main | (intros; apply GlobalTheory.PELOfUnif.main <;> assumption)
