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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.sqrt_one_add :
    ∀ {B : Type} [CommRing B] (I : Ideal B) [HenselianRing B I] (a : B), IsUnit (2 : B) → a - 1 ∈ I → ∃ α : Bˣ, (α : B) ^ 2 = a ∧ (α : B) - 1 ∈ I := by
  intro B _ I _ a h2 ha
  have hmon : (X ^ 2 - C a : B[X]).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    norm_num
  obtain ⟨α, hroot, hα⟩ := HenselianRing.is_henselian (X ^ 2 - C a) hmon 1
    (by
      have : (X ^ 2 - C a : B[X]).eval 1 = -(a - 1) := by simp <;> ring
      rw [this]
      exact I.neg_mem ha)
    (by
      have : (derivative (X ^ 2 - C a : B[X])).eval 1 = 2 := by
        simp only [derivative_sub, derivative_X_pow, derivative_C, eval_sub, eval_mul, eval_C,
          eval_pow, eval_one, eval_zero]
        norm_num
      rw [this]
      exact h2.map _)
  have hu : IsUnit α := by
    have hj := HenselianRing.jac (I := I) hα
    rw [Ideal.mem_jacobson_bot] at hj
    have := hj 1
    simpa using this
  refine ⟨hu.unit, ?_, ?_⟩
  · simp only [IsUnit.unit_spec]
    have := hroot
    simp [Polynomial.IsRoot] at this
    exact sub_eq_zero.mp this
  · simpa using hα
