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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_sumval :
    ∀ (M : ℤ), M ≠ 0 → ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) → ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l ≤ Real.log |(M : ℝ)| := by
  intro M hM T hT
  have hN : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hlog : Real.log |(M : ℝ)| = Real.log (M.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hlog, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l
      = ∑ l ∈ T, (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Nat.factorization_def _ (hT l hl)]
        rfl
    _ = ∑ l ∈ T.filter (· ∈ M.natAbs.factorization.support),
          (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne fun l _ h => ?_).symm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply h
        simp [h0]
    _ ≤ ∑ p ∈ M.natAbs.factorization.support,
          (M.natAbs.factorization p : ℝ) * Real.log p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_
        · intro x hx
          exact (Finset.mem_filter.mp hx).2
        · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)
