import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBetweenFinsetAndOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_between_finset_and_open' : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (V : X.Opens), V ≤ W → ∀ s : Finset X, (∀ x ∈ s, x ∈ V) → ∃ f : Γ(X, W), X.basicOpen f ≤ V ∧ ∀ x ∈ s, x ∈ X.basicOpen f := by
  first | exact @GlobalTheory.Mum.exists_basicOpen_between_finset_and_open | exact GlobalTheory.Mum.exists_basicOpen_between_finset_and_open | (intros; apply GlobalTheory.Mum.exists_basicOpen_between_finset_and_open <;> assumption)
