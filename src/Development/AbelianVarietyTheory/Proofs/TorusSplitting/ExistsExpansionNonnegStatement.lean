import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsExpansionNonneg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_expandsF_nuGe_zero_of_intTh : GlobalTheory.UT.AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre), w₀.IsGen → ∀ th : GlobalTheory.UT.SecA A F 1, IntTh U.toUnifPre w₀ th → ∃ ϑ : Fam D.toPre F 1, U.ExpandsF F 1 w₀ th ϑ ∧ NuGe D Q F v 1 ϑ 0 := by
  first | exact @GlobalTheory.EtaVal.exists_expansion_nonneg | exact GlobalTheory.EtaVal.exists_expansion_nonneg | (intros; apply GlobalTheory.EtaVal.exists_expansion_nonneg <;> assumption)
