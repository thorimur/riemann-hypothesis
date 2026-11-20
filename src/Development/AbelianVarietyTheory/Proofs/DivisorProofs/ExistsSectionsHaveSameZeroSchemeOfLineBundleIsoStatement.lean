import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsHaveSameZeroSchemeOfLineBundleIso
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sectionsHaveSameZeroScheme_of_lineBundleIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M → ∃ τ : M.Sec, SameDiv σ τ := by
  first | exact @GlobalTheory.LogPair.exists_sameDiv_of_lbIso | exact GlobalTheory.LogPair.exists_sameDiv_of_lbIso | (intros; apply GlobalTheory.LogPair.exists_sameDiv_of_lbIso <;> assumption)
