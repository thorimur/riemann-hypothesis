import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryHaarSmallBallLowerBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryHaar_smallBall_lower_bound : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → c * δ ^ D ≤ (muK ε {k | Formalism.REAL.hs (toMK k - 1) ≤ δ}).toReal := by
  first | exact @GlobalTheory.HaarSmallBall.smallBall | exact GlobalTheory.HaarSmallBall.smallBall | (intros; apply GlobalTheory.HaarSmallBall.smallBall <;> assumption)
