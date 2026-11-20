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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace KStar.TotallyRealRoots

private def sieveOK (n : ℕ) : Bool :=
  decide (2 ≤ n) && [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31].all (fun d => n == d || n % d != 0)

private def headF (n : ℕ) : ℕ :=
  if sieveOK n then (Nat.log2 (n ^ 256) + 1) * 1000000 / n ^ 2 + 1 else 0

private theorem tail_step (m : ℝ) (hm : 1 ≤ m) :
    Real.log (m + 1) / (m + 1) ^ 2 ≤ (Real.log m + 2) / m - (Real.log (m + 1) + 2) / (m + 1) := by
  have hm0 : 0 < m := by linarith
  have hL : 0 ≤ Real.log (m + 1) := Real.log_nonneg (by linarith)
  have h1 : Real.log (m + 1) - Real.log m ≤ 1 / m := by
    rw [← Real.log_div (by linarith) hm0.ne']
    have := Real.log_le_sub_one_of_pos (x := (m + 1) / m) (by positivity)
    have e : (m + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  set L := Real.log (m + 1)
  have h2 : (L - 1 / m + 2) / m ≤ (Real.log m + 2) / m := by
    apply div_le_div_of_nonneg_right _ hm0.le
    linarith
  have h3 : (L - 1 / m + 2) / m - (L + 2) / (m + 1) - L / (m + 1) ^ 2
      = L / (m * (m + 1) ^ 2) + (m - 1) / (m ^ 2 * (m + 1)) := by
    field_simp
    ring
  have h4 : 0 ≤ L / (m * (m + 1) ^ 2) := by positivity
  have h5 : 0 ≤ (m - 1) / (m ^ 2 * (m + 1)) := div_nonneg (by linarith) (by positivity)
  linarith

private theorem tail_sum (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    ∑ n ∈ Finset.Ico (N + 1) (N + 1 + k), Real.log n / (n : ℝ) ^ 2
      ≤ (Real.log N + 2) / N - (Real.log ((N + k : ℕ) : ℝ) + 2) / ((N + k : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc (N + 1), Finset.sum_Ico_succ_top (by omega)]
    have h := tail_step ((N + k : ℕ) : ℝ) (by exact_mod_cast (by omega : 1 ≤ N + k))
    have e1 : ((N + 1 + k : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
    have e2 : ((N + (k + 1) : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e1, e2]
    linarith

end KStar.TotallyRealRoots
