import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.UltrametricPowerBound

variable {l : ℕ} [Fact (Nat.Prime l)]

lemma ultra (q r : ℚ_[l]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := Padic.nonarchimedean q r

lemma pow_sub_one_le (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) : ‖w ^ k - 1‖ ≤ ‖w - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 = w * (w ^ k - 1) + (w - 1) := by ring
    rw [e]
    refine (ultra _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖w‖ * ‖w ^ k - 1‖ ≤ 1 * ‖w ^ k - 1‖ := by gcongr
      _ ≤ ‖w - 1‖ := by rw [one_mul]; exact ih

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (w : ℚ_[l]), ‖w‖ ≤ (1 : ℝ) → ∀ (k : ℕ),
    ‖w ^ k - (1 : ℚ_[l]) - (↑k : ℚ_[l]) * (w - (1 : ℚ_[l]))‖ ≤ ‖w - (1 : ℚ_[l])‖ ^ (2 : ℕ) := by
  intro l _ w hw k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℚ_[l]) * (w - 1)
        = (w ^ k - 1 - (k : ℚ_[l]) * (w - 1)) + (w - 1) * (w ^ k - 1) := by push_cast; ring
    rw [e]
    refine (ultra _ _).trans (max_le ih ?_)
    rw [norm_mul, sq]
    exact mul_le_mul_of_nonneg_left (pow_sub_one_le w hw k) (norm_nonneg _)

end GlobalTheory.UltrametricPowerBound
