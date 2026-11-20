import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshPullbackHolomorphic
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psh_pullback_holomorphic : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (n : ℕ) (Y : Type)
    [TopologicalSpace Y] (B : FinHolAtlas n Y) (μ : Y → X) (hμ : HoloMap B A μ) (P : LocPot X),
    IsPotential A P → IsPsh A P → IsPsh B (P.pullback μ hμ.1) := by
  first | exact @GlobalTheory.PshPull.isPsh_pullback | exact GlobalTheory.PshPull.isPsh_pullback | (intros; apply GlobalTheory.PshPull.isPsh_pullback <;> assumption)
