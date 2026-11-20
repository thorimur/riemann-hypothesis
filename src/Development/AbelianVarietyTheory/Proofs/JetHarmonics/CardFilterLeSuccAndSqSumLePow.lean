import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem card_filter_le_succ_and_sq_sum_le_pow : ∀ (n kk : ℕ) (bv : ℝ), 1 ≤ kk → kk + 1 ≤ n → (n : ℝ) ≤ bv → (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk ∧ (18 / 13 : ℝ) ^ 2 + ((n + 1 - kk : ℕ) : ℝ) * (3 * (6 * bv) ^ (n - kk)) ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) := by
  intro n kk bv h1 h2 h3
  refine ⟨?_, ?_⟩
  · have hlt : kk - 1 < n := by omega
    have : (univ.filter fun a : Fin n => kk ≤ a.val + 1) = Finset.Ici (⟨kk - 1, hlt⟩ : Fin n) := by
      ext a
      simp only [mem_filter, mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
      omega
    rw [this, Fin.card_Ici]
    simp only
    omega
  · have e1 : n + 1 - kk = (n - kk) + 1 := by omega
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hM : ((n + 1 - kk : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n + 1 - kk ≤ n)
    have hb : (2 : ℝ) ≤ bv := hn2.trans h3
    have hX : (1 : ℝ) ≤ (6 * bv) ^ (n - kk) := one_le_pow₀ (by linarith)
    have e2 : (6 * bv) ^ (2 * (n + 1 - kk)) = 36 * bv ^ 2 * ((6 * bv) ^ (n - kk)) ^ 2 := by
      rw [e1]; ring
    rw [e2]
    set X := (6 * bv) ^ (n - kk)
    set c := ((n + 1 - kk : ℕ) : ℝ)
    have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ hX
    have hc : c ≤ bv := hM.trans h3
    have h4 : c * X ^ 2 ≤ bv * X ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have h5 : (9 * bv + 2) * X ^ 2 ≤ 36 * bv ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    nlinarith

end GlobalTheory
