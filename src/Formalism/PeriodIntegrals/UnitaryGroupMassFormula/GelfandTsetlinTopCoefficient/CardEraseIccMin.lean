import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

namespace PI.GTNum

open Finset

theorem sum_range_le_tele (n : ℕ) (a t : ℕ → ℤ) (h : ∀ i < n, a i ≤ t i - t (i + 1)) :
    ∑ i ∈ range n, a i ≤ t 0 - t n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    linarith

theorem card_erase_Icc_min (a b c x : ℤ) (hab : a ≤ b) (hc : 0 ≤ c)
    (hx : x ∈ Icc a (min b (a + c))) :
    ((((Icc a (min b (a + c))).erase x).card : ℕ) : ℤ) = min (b - a) c := by
  rw [Finset.card_erase_of_mem hx, Int.card_Icc]
  have h1 : 1 ≤ (min b (a + c) + 1 - a).toNat := by omega
  rw [Nat.cast_sub h1, Int.toNat_of_nonneg (by omega)]
  push_cast
  omega

theorem abs_prod_le_prod {α : Type*} (s : Finset α) (f b : α → ℤ) (h : ∀ x ∈ s, |f x| ≤ b x) :
    |∏ x ∈ s, f x| ≤ ∏ x ∈ s, b x := by
  rw [abs_prod]
  exact Finset.prod_le_prod (fun x _ => abs_nonneg _) h

theorem abs_prod_le_pow {α : Type*} (s : Finset α) (f : α → ℤ) (B : ℤ) (h : ∀ x ∈ s, |f x| ≤ B) :
    |∏ x ∈ s, f x| ≤ B ^ s.card := by
  simpa [Finset.prod_const] using abs_prod_le_prod s f (fun _ => B) h

theorem prod_pow_pow {α : Type*} (s : Finset α) (B : ℤ) (m : ℕ) (e : α → ℕ) :
    ∏ x ∈ s, (B ^ m) ^ e x = B ^ (m * ∑ x ∈ s, e x) := by
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]

theorem abs_factor_le (v s L S : ℤ) (i j n : ℕ) (hi : i < n) (hj : j < n)
    (hv1 : L ≤ v) (hv2 : v ≤ S + (S - L)) (hs1 : L ≤ s) (hs2 : s ≤ S) :
    |v - (i : ℤ) - s + (j : ℤ)| ≤ 2 * (S - L) + ((n + 1 : ℕ) : ℤ) := by
  rw [abs_le]
  push_cast
  constructor <;> omega

end PI.GTNum
