import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleTopSelfIntersectionPos
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_lineBundle_top_selfIntersection_pos : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X = (d : ℕ) → ∀ A : LB X, IsAmpleLB A → 0 < topSelfIntersection k A d := by
  first | exact @GlobalTheory.AmplePos.topSelf_pos | exact GlobalTheory.AmplePos.topSelf_pos | (intros; apply GlobalTheory.AmplePos.topSelf_pos <;> assumption)
