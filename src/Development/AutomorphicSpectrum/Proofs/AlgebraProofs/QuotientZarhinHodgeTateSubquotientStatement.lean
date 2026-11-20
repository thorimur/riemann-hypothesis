import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientZarhinHodgeTateSubquotient
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_zarhin_hodge_tate_subquotient : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement → SubquotientStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate | exact GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.subquotientStatement_of_quotient_zarhin_hodgeTate <;> assumption)
