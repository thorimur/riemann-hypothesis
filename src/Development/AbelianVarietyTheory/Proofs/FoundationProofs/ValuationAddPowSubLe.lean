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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory.AlmostEt

open scoped NNReal

theorem valuation_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) :
    v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (v.map_add _ _).trans (max_le ih (by simp))

theorem valuation_add_pow_sub_le (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ)
    (hp : p.Prime) (y β : L) :
    v ((y + β) ^ p - y ^ p - β ^ p) ≤ v (p : L) * v β * (max (v y) (v β)) ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have key : (y + β) ^ (q + 1) - y ^ (q + 1) - β ^ (q + 1) =
      ∑ i ∈ Finset.range q, y ^ (i + 1) * β ^ (q + 1 - (i + 1)) * ((q + 1).choose (i + 1) : L) := by
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp
  rw [key]
  apply Valuation.map_sum_le
  intro i hi
  have hi : i < q := Finset.mem_range.mp hi
  set M := max (v y) (v β)
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (Nat.succ_ne_zero i) (by omega)
  have hsub : q + 1 - (i + 1) = (q - (i + 1)) + 1 := by omega
  rw [hk, hsub]
  push_cast
  simp only [map_mul, map_pow]
  have h1 : v y ^ (i + 1) ≤ M ^ (i + 1) := pow_le_pow_left₀ (by positivity) (le_max_left _ _) _
  have h2 : v β ^ (q - (i + 1)) ≤ M ^ (q - (i + 1)) := pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
  have h3 : v (k : L) ≤ 1 := valuation_natCast_le_one v k
  have hM : M ^ (i + 1) * M ^ (q - (i + 1)) = M ^ q := by
    rw [← pow_add]; congr 1; omega
  rw [pow_succ (v β)]
  calc _ ≤ M ^ (i + 1) * (M ^ (q - (i + 1)) * v β) * (v ((q : L) + 1) * 1) := by gcongr
    _ = _ := by simp only [Nat.add_sub_cancel, ← hM]; ring

end GlobalTheory.AlmostEt
