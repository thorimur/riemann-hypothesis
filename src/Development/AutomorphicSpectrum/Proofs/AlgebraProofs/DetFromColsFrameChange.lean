import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Matrix.ColumnRowPartitioned
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

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix

theorem det_fromCols_frame_change : ∀ (R : Type) [CommRing R] (p q : ℕ) (J J₂ : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S S₂ : Matrix (Fin q) (Fin p ⊕ Fin q) R) (T T₂ : Matrix (Fin p ⊕ Fin q) (Fin q) R) (A : Matrix (Fin p) (Fin p) R) (B : Matrix (Fin q) (Fin q) R), S * J = 0 → S * T = 1 → IsUnit (Matrix.fromCols J T).det → S₂ * T₂ = 1 → J₂ = J * A → S = B * S₂ → (Matrix.fromCols J₂ T₂).det = (Matrix.fromCols J T).det * A.det * B.det := by
  intro R _ p q J J₂ S S₂ T T₂ A B hSJ hST hU hST₂ hJ hS
  set W : Matrix (Fin p ⊕ Fin q) (Fin q) R := (Matrix.fromCols J T)⁻¹ * T₂ with hW
  have h1 : Matrix.fromCols J T * W = T₂ := by
    rw [hW, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have h2 : J * W.toRows₁ + T * W.toRows₂ = T₂ := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromRows_toRows, h1]
  have h3 : W.toRows₂ = B := by
    have h := congrArg (fun X => S * X) h2
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hSJ, hST, Matrix.zero_mul, Matrix.one_mul,
      zero_add] at h
    rw [h, hS, Matrix.mul_assoc, hST₂, Matrix.mul_one]
  have h4 : Matrix.fromCols J₂ T₂ =
      Matrix.fromCols J T * Matrix.fromBlocks A W.toRows₁ 0 B := by
    rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, ← hJ, ← h3, h2]
  rw [h4, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat
