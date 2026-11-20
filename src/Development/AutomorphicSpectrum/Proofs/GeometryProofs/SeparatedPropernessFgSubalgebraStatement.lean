import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SeparatedPropernessFgSubalgebra
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.separated_properness_fg_subalgebra : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), IsSeparated p → LocallyOfFiniteType p → QuasiCompact p → IsProper (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsProper (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends | exact GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.isProper_descends <;> assumption)
