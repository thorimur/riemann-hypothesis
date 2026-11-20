import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroExpansionTermCompleteDVR
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_expansionTerm_completeDVR : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G'), GlobalTheory.LN.Under U' U₀.toUnifPre → ∀ (σ' : U'.SecGT (𝟙_ _) 1) (f' : ∀ α, GlobalTheory.UU.SecBT D'.toPre (𝟙_ _) 1 α), U'.ExpT (𝟙_ _) 1 σ' f' → (∃ j, σ'.f j ≠ 0) → ∃ α j, (f' α).f j ≠ 0 := by
  first | exact @GlobalTheory.ExpansionNonzero.exists_term_ne_zero | exact GlobalTheory.ExpansionNonzero.exists_term_ne_zero | (intros; apply GlobalTheory.ExpansionNonzero.exists_term_ne_zero <;> assumption)
