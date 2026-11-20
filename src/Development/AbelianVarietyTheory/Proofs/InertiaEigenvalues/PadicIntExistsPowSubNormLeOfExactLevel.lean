import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory

theorem padicInt_exists_pow_sub_norm_le_of_exact_level (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ)
    (hm : 1 ≤ m) (hu : ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m)
    (hv : ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m) :
    ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  have key : ∀ (x : ℤ_[l]) (n : ℕ), ‖x‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ n ↔ ((l : ℕ) : ℤ_[l]) ^ n ∣ x := by
    intro x n
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_p,
      zpow_neg, zpow_natCast, inv_pow]
  have hl0 : ‖((l : ℕ) : ℤ_[l])‖ ^ m ≠ 0 := by
    apply pow_ne_zero
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨a, ha⟩ := (key _ _).1 hu.le
  obtain ⟨b, hb⟩ := (key _ _).1 hv
  have ha1 : ‖a‖ = 1 := by
    rw [ha, norm_mul, norm_pow] at hu
    exact mul_left_cancel₀ hl0 (by rw [hu, mul_one])
  obtain ⟨a', ha'⟩ := (PadicInt.isUnit_iff.2 ha1).exists_right_inv
  refine ⟨(a' * b).appr 1, (key _ _).2 ?_⟩
  set i := (a' * b).appr 1 with hi
  have hc := PadicInt.appr_spec 1 (a' * b)
  rw [Ideal.mem_span_singleton, pow_one, ← hi] at hc
  obtain ⟨c, hc⟩ := hc
  have hu' : u = 1 + ((l : ℕ) : ℤ_[l]) ^ m * a := by rw [← ha]; ring
  have hv' : v = 1 + ((l : ℕ) : ℤ_[l]) ^ m * b := by rw [← hb]; ring
  have hpow : ∀ (x : ℤ_[l]) (n : ℕ), ∃ d, (1 + x) ^ n = 1 + n * x + x ^ 2 * d := by
    intro x n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨d + n + x * d, by rw [pow_succ, hd]; push_cast; ring⟩
  obtain ⟨d, hd⟩ := hpow (((l : ℕ) : ℤ_[l]) ^ m * a) i
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine ⟨-(a * c) + ((l : ℕ) : ℤ_[l]) ^ k * a ^ 2 * d, ?_⟩
  have hi' : (i : ℤ_[l]) = a' * b - ((l : ℕ) : ℤ_[l]) * c := by rw [← hc]; ring
  rw [hu', hd, hv', hi']
  linear_combination (((l : ℕ) : ℤ_[l]) ^ (1 + k) * b) * ha'

end GlobalTheory
