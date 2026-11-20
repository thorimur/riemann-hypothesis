import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveIsoG_unique_on_abelian : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t, IsPrimG t wP → IsPrimG t wP' → wP = wP' := by
  first | exact @GlobalTheory.isPrimG_unique | exact GlobalTheory.isPrimG_unique | (intros; apply GlobalTheory.isPrimG_unique <;> assumption)
