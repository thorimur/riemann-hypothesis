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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.SquareDistanceExpansion

open Matrix

theorem expand {R : Type} [CommRing R] {n : ℕ} (X Y X' Y' : Matrix (Fin n) (Fin n) R) :
    (1 + X + Y) * (1 + X' + Y') = 1 + X + Y + X' + Y' + X * X' + X * Y' + Y * X' + Y * Y' := by
  noncomm_ring

theorem sq_id {R : Type} [CommRing R] {d : ℕ} (H H' : Matrix (Fin d) (Fin d) R) :
    H * H' - 1 = (H - 1) + (H' - 1) + (H - 1) * (H' - 1) := by
  noncomm_ring

theorem prod_eq {R : Type} [CommRing R] {n d : ℕ} (a c : Matrix (Fin n) (Fin d) R)
    (α γ : Matrix (Fin d) (Fin n) R) (M N : Matrix (Fin d) (Fin d) R) :
    a * M * α * (c * N * γ) = a * M * (α * c) * N * γ := by
  simp only [Matrix.mul_assoc]

theorem dist {R : Type} [CommRing R] {n d : ℕ} (a : Matrix (Fin n) (Fin d) R)
    (α : Matrix (Fin d) (Fin n) R) (A B : Matrix (Fin d) (Fin d) R) :
    a * (A + B + A * B) * α = a * A * α + a * B * α + a * A * B * α := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem main : (let d1 : {R : Type} → [CommRing R] → {n d : ℕ} → Matrix (Fin n) (Fin d) R → Matrix (Fin n) (Fin d) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin n) R → Matrix (Fin d) (Fin d) R → Matrix (Fin d) (Fin d) R → Matrix (Fin n) (Fin n) R := @(fun {R : Type} [CommRing R] {n d : ℕ} (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) ↦ (1 : Matrix (Fin n) (Fin n) R) + a * (H - (1 : Matrix (Fin d) (Fin d) R)) * α + b * (K - (1 : Matrix (Fin d) (Fin d) R)) * β); ∀ {R : Type} [inst : CommRing R] {n d : ℕ} {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}, α * a = (1 : Matrix (Fin d) (Fin d) R) → β * b = (1 : Matrix (Fin d) (Fin d) R) → α * b = (0 : Matrix (Fin d) (Fin d) R) → β * a = (0 : Matrix (Fin d) (Fin d) R) → ∀ (H K H' K' : Matrix (Fin d) (Fin d) R), d1 a b α β H K * d1 a b α β H' K' = d1 a b α β (H * H') (K * K')) := by
  dsimp only
  intro R _ n d a b α β hαa hβb hαb hβa H K H' K'
  have e1 := prod_eq a a α α (H - 1) (H' - 1)
  have e2 := prod_eq a b α β (H - 1) (K' - 1)
  have e3 := prod_eq b a β α (K - 1) (H' - 1)
  have e4 := prod_eq b b β β (K - 1) (K' - 1)
  rw [hαa, Matrix.mul_one] at e1
  rw [hαb, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e2
  rw [hβa, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul] at e3
  rw [hβb, Matrix.mul_one] at e4
  rw [expand, e1, e2, e3, e4, sq_id H H', sq_id K K', dist a α (H - 1) (H' - 1),
    dist b β (K - 1) (K' - 1)]
  abel

end GlobalTheory.SquareDistanceExpansion
