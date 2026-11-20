import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTransitionCompatibleFrames_of_no_completeDVR_points : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ), 1 ≤ n' → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z)) → HasFrames G L N A n r s → HasFrames G L N A n' r s := by
  first | exact @GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty | exact GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty | (intros; apply GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty <;> assumption)
