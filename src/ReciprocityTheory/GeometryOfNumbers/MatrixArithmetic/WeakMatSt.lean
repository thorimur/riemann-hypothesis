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

namespace ReciprocityTheory.GeometryOfNumbersTheory

theorem wma_sum_log_le {ι : Type} [Fintype ι] [Nonempty ι] (t : ι → ℝ) (ht : ∀ σ, 0 ≤ t σ) :
    ∑ σ, Real.log (1 + t σ) ≤
      Fintype.card ι * Real.log (1 + (∑ σ, t σ) / Fintype.card ι) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  set M := 1 + (∑ σ, t σ) / Fintype.card ι with hM
  have hM0 : 0 < M := by
    have : 0 ≤ (∑ σ, t σ) / Fintype.card ι := div_nonneg (Finset.sum_nonneg fun σ _ => ht σ) hN.le
    linarith
  have hpt : ∀ σ, Real.log (1 + t σ) ≤ Real.log M + ((1 + t σ) / M - 1) := fun σ => by
    have hy : 0 < 1 + t σ := by linarith [ht σ]
    have := Real.log_le_sub_one_of_pos (div_pos hy hM0)
    rw [Real.log_div hy.ne' hM0.ne'] at this
    linarith
  refine (Finset.sum_le_sum fun σ _ => hpt σ).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_sub_distrib,
    ← Finset.sum_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card ι : ℝ) * 1 + ∑ σ, t σ = Fintype.card ι * M := by
    rw [hM]; field_simp
  rw [this, mul_div_cancel_right₀ _ hM0.ne']
  ring

end ReciprocityTheory.GeometryOfNumbersTheory
