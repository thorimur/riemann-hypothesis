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

namespace GlobalTheory.AbelianSumIdentitySecond

open Matrix

theorem main {R : Type} [CommRing R] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) R}
    {Xs Ys : Matrix (Fin r) (Fin n) R}
    (h1 : Xs * X = (0 : Matrix (Fin r) (Fin r) R)) (h2 : Ys * Y = (0 : Matrix (Fin r) (Fin r) R))
    (h3 : Xs * Y = (1 : Matrix (Fin r) (Fin r) R)) (h4 : Ys * X = (1 : Matrix (Fin r) (Fin r) R))
    (A B A' B' : Matrix (Fin r) (Fin r) R) :
    ((1 : Matrix (Fin n) (Fin n) R) + X * A * Ys + Y * B * Xs) *
        ((1 : Matrix (Fin n) (Fin n) R) + X * A' * Ys + Y * B' * Xs) =
      (1 : Matrix (Fin n) (Fin n) R) + X * (A + A' + A * A') * Ys + Y * (B + B' + B * B') * Xs := by
  have e1 : X * A * Ys * (X * A' * Ys) = X * (A * A') * Ys := by
    calc X * A * Ys * (X * A' * Ys) = X * A * (Ys * X) * A' * Ys := by
          simp only [Matrix.mul_assoc]
      _ = X * (A * A') * Ys := by rw [h4, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e2 : X * A * Ys * (Y * B' * Xs) = 0 := by
    calc X * A * Ys * (Y * B' * Xs) = X * A * (Ys * Y) * B' * Xs := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h2]; simp
  have e3 : Y * B * Xs * (X * A' * Ys) = 0 := by
    calc Y * B * Xs * (X * A' * Ys) = Y * B * (Xs * X) * A' * Ys := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h1]; simp
  have e4 : Y * B * Xs * (Y * B' * Xs) = Y * (B * B') * Xs := by
    calc Y * B * Xs * (Y * B' * Xs) = Y * B * (Xs * Y) * B' * Xs := by
          simp only [Matrix.mul_assoc]
      _ = Y * (B * B') * Xs := by rw [h3, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, e1, e2, e3, e4]
  abel

end GlobalTheory.AbelianSumIdentitySecond

example : ∀ {R : Type} [inst : CommRing R] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) R} {Xs Ys : Matrix (Fin r) (Fin n) R}, Xs * X = (0 : Matrix (Fin r) (Fin r) R) → Ys * Y = (0 : Matrix (Fin r) (Fin r) R) → Xs * Y = (1 : Matrix (Fin r) (Fin r) R) → Ys * X = (1 : Matrix (Fin r) (Fin r) R) → ∀ (A B A' B' : Matrix (Fin r) (Fin r) R), ((1 : Matrix (Fin n) (Fin n) R) + X * A * Ys + Y * B * Xs) * ((1 : Matrix (Fin n) (Fin n) R) + X * A' * Ys + Y * B' * Xs) = (1 : Matrix (Fin n) (Fin n) R) + X * (A + A' + A * A') * Ys + Y * (B + B' + B * B') * Xs := @GlobalTheory.AbelianSumIdentitySecond.main
