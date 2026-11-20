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
import Mathlib.RingTheory.PiTensorProduct
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

namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives

open ReciprocityTheory.ChartRestriction.G.TB MvPolynomial

variable {R : Type} [CommRing R] {p q n : ℕ}

def ySide (e : Fin p → Fin n → R) (b : Fin q) :
    Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R) where
  carrier := {B | (∀ j, pderiv (Sum.inl j) B = 0) ∧
    (∀ j j', pderiv (Sum.inl j') (pderiv (Sum.inr j) B) = 0) ∧
    (∀ b', ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) B = 0)}
  mul_mem' := by
    rintro A B ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩
    · simp [hA1, hB1]
    · simp [hA1, hB1, hA2, hB2]
    · have : ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) (A * B)
          = (∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) A) * B
            + A * ∑ k, C (e b' k) * pderiv (Sum.inr (b, k)) B := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [pderiv_mul]; ring
      rw [this, hA3, hB3]; ring
  add_mem' := by
    rintro A B ⟨hA1, hA2, hA3⟩ ⟨hB1, hB2, hB3⟩
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩
    · simp [hA1, hB1]
    · simp [hA2, hB2]
    · simp only [map_add, mul_add, Finset.sum_add_distrib, hA3, hB3, add_zero]
  algebraMap_mem' := by
    intro r
    refine ⟨fun j => ?_, fun j j' => ?_, fun b' => ?_⟩ <;> simp [MvPolynomial.algebraMap_eq]

def xSide (e : Fin p → Fin n → R) (a : Fin p) (b : Fin q) :
    Subalgebra R (MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R) where
  carrier := {A | (∀ j, pderiv (Sum.inr j) A = 0) ∧
    ∀ B ∈ ySide e b, ∑ k, pderiv (Sum.inl (a, k)) A * pderiv (Sum.inr (b, k)) B = 0}
  mul_mem' := by
    rintro A A' ⟨hA1, hA2⟩ ⟨hA'1, hA'2⟩
    refine ⟨fun j => ?_, fun B hB => ?_⟩
    · simp [hA1, hA'1]
    · have : ∑ k, pderiv (Sum.inl (a, k)) (A * A') * pderiv (Sum.inr (b, k)) B
          = A' * (∑ k, pderiv (Sum.inl (a, k)) A * pderiv (Sum.inr (b, k)) B)
            + A * ∑ k, pderiv (Sum.inl (a, k)) A' * pderiv (Sum.inr (b, k)) B := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [pderiv_mul]; ring
      rw [this, hA2 B hB, hA'2 B hB]; ring
  add_mem' := by
    rintro A A' ⟨hA1, hA2⟩ ⟨hA'1, hA'2⟩
    refine ⟨fun j => ?_, fun B hB => ?_⟩
    · simp [hA1, hA'1]
    · simp only [map_add, add_mul, Finset.sum_add_distrib, hA2 B hB, hA'2 B hB, add_zero]
  algebraMap_mem' := by
    intro r
    refine ⟨fun j => ?_, fun B _ => ?_⟩ <;> simp [MvPolynomial.algebraMap_eq]

end PI.UnitaryGroupMassFormula.FormPartialDerivatives
