import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforward
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmpleCechLineBundle_disjointUnion_pushforward : ∀ (Z Z₁ Z₂ : Scheme.{0}) (f₁ : Z₁ ⟶ Z) (f₂ : Z₂ ⟶ Z) [IsOpenImmersion f₁] [IsOpenImmersion f₂] (A₁ : LB Z₁) (A₂ : LB Z₂), IsCompl (Set.range f₁) (Set.range f₂) → A₁.IsLB → A₂.IsLB → AmpleFam A₁ → AmpleFam A₂ → (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)).IsLB ∧ AmpleFam (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)) := by
  first | exact @GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | exact GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | (intros; apply GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam <;> assumption)
