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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory

theorem cone_ratio_bounded (a : ℕ) (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      ∀ p q : Fin a, p ≤ q → r q / r p ≤ C := by
  have hM : (1 : ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 t⁻¹ := le_trans zero_le_one hM
  refine ⟨(max 1 t⁻¹) ^ a, pow_nonneg hM0 _, fun r hr hstep p q hpq => ?_⟩
  have key : ∀ (n : ℕ) (h : (p : ℕ) + n < a), r ⟨p + n, h⟩ ≤ (max 1 t⁻¹) ^ n * r p := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      have h' : (p : ℕ) + n < a := by omega
      have h1 := hstep ⟨p + n, h'⟩ ⟨p + (n + 1), h⟩ (by simp [add_assoc])
      have h2 : r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩ := by
        rw [inv_mul_eq_div, le_div_iff₀ ht, mul_comm]; exact h1
      calc r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩ := h2
        _ ≤ max 1 t⁻¹ * r ⟨p + n, h'⟩ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hr _).le
        _ ≤ max 1 t⁻¹ * ((max 1 t⁻¹) ^ n * r p) := mul_le_mul_of_nonneg_left (ih h') hM0
        _ = (max 1 t⁻¹) ^ (n + 1) * r p := by ring
  have hpq' : (p : ℕ) ≤ q := hpq
  have hlt : (p : ℕ) + (q - p) < a := by have := q.2; omega
  have hq : (⟨p + (q - p), hlt⟩ : Fin a) = q := Fin.ext (by simp only; omega)
  have h3 := key (q - p) hlt
  rw [hq] at h3
  rw [div_le_iff₀ (hr p)]
  refine h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM ?_) (hr p).le)
  have := q.2; omega

end GlobalTheory
