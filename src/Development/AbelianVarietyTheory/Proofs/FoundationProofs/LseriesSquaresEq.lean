import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LucasLehmer
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open Complex Filter Topology

namespace GlobalTheory

theorem lseriesSquares_term (e : ℕ) (c : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) (d : ℕ) :
    LSeries.term (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
        c (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) (d * d)
      = LSeries.term c ((e + 1 : ℕ) + 2 * s) d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [LSeries.term_of_ne_zero (mul_ne_zero hd hd), LSeries.term_of_ne_zero hd]
  simp only [Nat.sqrt_eq, if_true]
  rw [Nat.cast_mul, natCast_mul_natCast_cpow, ← cpow_add _ _ hd', ← cpow_natCast, mul_div_assoc,
    ← cpow_sub _ _ hd', div_eq_mul_inv, ← cpow_neg]
  congr 2
  have h3 : 1 ≤ 3 * e := by omega
  push_cast [Nat.cast_sub h3]
  ring

theorem lseriesSquares_eq : ∀ (e : ℕ) (χ ψ θ : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → LSeriesSummable (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) ∧ LSeries (fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
  intro e χ ψ θ s he hs hb
  have hinj : Function.Injective (fun d : ℕ => d * d) := fun a b h => Nat.mul_self_inj.mp h
  have hterm := lseriesSquares_term e (fun n => χ n * ψ n * θ n) s he
  set f : ℕ → ℂ := fun n : ℕ => if Nat.sqrt n * Nat.sqrt n = n then
    χ (Nat.sqrt n) * ψ (Nat.sqrt n) * θ (Nat.sqrt n) * (Nat.sqrt n : ℂ) ^ (3 * e - 1) else 0 with hf
  have hzero : ∀ n, n ∉ Set.range (fun d : ℕ => d * d) →
      LSeries.term f (((2 * (e : ℝ) + s : ℝ)) : ℂ) n = 0 := by
    intro n hn
    have hn' : ¬ (Nat.sqrt n * Nat.sqrt n = n) := fun h => hn ⟨_, h⟩
    rw [LSeries.term_def]
    split_ifs
    · rfl
    · simp [hf, hn']
  have hsum : LSeriesSummable (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) ?_
    · obtain ⟨h1, h2, h3⟩ := hb n
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3
    · have : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      simp
      linarith
  constructor
  · refine (hinj.summable_iff hzero).mp ?_
    exact (show Summable _ from hsum).congr fun d => (hterm d).symm
  · unfold LSeries
    rw [← hinj.tsum_eq (fun n hn => by
      by_contra h
      exact hn (hzero n h))]
    exact tsum_congr hterm

end GlobalTheory
