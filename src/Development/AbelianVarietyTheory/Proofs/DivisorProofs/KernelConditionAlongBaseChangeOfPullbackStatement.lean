import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionAlongBaseChangeOfPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_condition_along_baseChange_of_pullback : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S') [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over S) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), P₁.IsLB → IsGrpPullback A A₁ f φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → (∀ (T : Over S') (x : T ⟶ A), IsTrivial (slice A P x) → x = 1) → KerAlong A₁ P₁ f := by
  first | exact @GlobalTheory.PrincSubring.kerAlong_of_pull | exact GlobalTheory.PrincSubring.kerAlong_of_pull | (intros; apply GlobalTheory.PrincSubring.kerAlong_of_pull <;> assumption)
