import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left), IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → ∀ {S' : Scheme.{0}} (g : S' ⟶ S), KerAlong A P g ↔ GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A 8) (powLB A P) g := by
  first | exact @GlobalTheory.PrincSubring.kerAlong_iff_trivAlong | exact GlobalTheory.PrincSubring.kerAlong_iff_trivAlong | (intros; apply GlobalTheory.PrincSubring.kerAlong_iff_trivAlong <;> assumption)
