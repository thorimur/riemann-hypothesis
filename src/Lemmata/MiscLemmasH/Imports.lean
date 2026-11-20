import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.RingTheory.Henselian
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

open TensorProduct IsLocalRing Polynomial

namespace Bl.SecondBlockLemmaI

variable {A : Type} [CommRing A] (I : Ideal A)

theorem goal1 [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  have hm : (X ^ 2 - X : A[X]).Monic := by
    exact monic_X_pow_sub (lt_of_le_of_lt degree_X_le (by norm_num))
  have h0 : (X ^ 2 - X : A[X]).eval ε ∈ I := by
    simp only [eval_sub, eval_pow, eval_X]
    rw [pow_two]; exact h
  have hu : IsUnit (Ideal.Quotient.mk I ((X ^ 2 - X : A[X]).derivative.eval ε)) := by
    have hd : (X ^ 2 - X : A[X]).derivative.eval ε = 2 * ε - 1 := by
      simp only [derivative_sub, derivative_X_pow, derivative_X, eval_sub, eval_mul, eval_pow,
        eval_X, eval_one, eval_C]
      norm_num
    rw [hd]
    have hsq : (2 * ε - 1) * (2 * ε - 1) = 1 + 4 * (ε * ε - ε) := by ring
    have hq : Ideal.Quotient.mk I ((2 * ε - 1) * (2 * ε - 1)) = 1 := by
      rw [hsq, map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_left 4 h), add_zero]
    rw [map_mul] at hq
    exact ⟨⟨_, _, hq, hq⟩, rfl⟩
  obtain ⟨a, ha, hae⟩ := HenselianRing.is_henselian (I := I) _ hm ε h0 hu
  refine ⟨a, ?_, hae⟩
  have := ha.eq_zero
  simp only [eval_sub, eval_pow, eval_X] at this
  rw [← pow_two]; exact sub_eq_zero.mp this

end Bl.SecondBlockLemmaI
