import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PrimitiveExpansionThetaPullbackHeisenbergTransla
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_expansion_thetaPullback_heisenbergTranslates : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ (m : ℕ), Odd m → IsUnit (m : V) → ∀ x t c s, x ^ (m ^ 2) = 1 → ThC A ρ m th x t c → U.ExpandsF F (m ^ 2) w₀ t s → Prim D Q v s := by
  first | exact @GlobalTheory.UT.PrimPull.main | exact GlobalTheory.UT.PrimPull.main | (intros; apply GlobalTheory.UT.PrimPull.main <;> assumption)
