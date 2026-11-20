import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfLieMultZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialGoodReduction_of_lieMult_zero : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (g : K →+* Ω) (σ : 𝓞 F →+* Ω), LieMult act (spMap g) σ 0 → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.PotGoodLie.potGood_of_lieMult_zero | exact GlobalTheory.PotGoodLie.potGood_of_lieMult_zero | (intros; apply GlobalTheory.PotGoodLie.potGood_of_lieMult_zero <;> assumption)
