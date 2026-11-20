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
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.MatrixComm

theorem commute_diagonal_of_dominated {n : ℕ} (d e : Fin n → ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Matrix.diagonal d * Z = Z * Matrix.diagonal d)
    (hde : ∀ i j, d i = d j → e i = e j) :
    Z * Matrix.diagonal e = Matrix.diagonal e * Z := by
  ext i j
  have hij := congrFun (congrFun hZ i) j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hij
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hz : Z i j = 0
  · simp [hz]
  · have hd : d i = d j := by
      have : Z i j * d i = Z i j * d j := by rw [mul_comm (Z i j) (d i)]; exact hij
      exact mul_left_cancel₀ hz this
    rw [hde i j hd, mul_comm]

theorem commute_of_dominated_diag {n : ℕ} (U H A Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hH : (Uᴴ * H * U).IsDiag) (hA : (Uᴴ * A * U).IsDiag)
    (hdom : ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → (Uᴴ * A * U) i i = (Uᴴ * A * U) j j)
    (hHY : H * Y = Y * H) : Y * A = A * Y := by
  have h2 : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have conj_mul : ∀ P Q : Matrix (Fin n) (Fin n) ℂ,
      (Uᴴ * P * U) * (Uᴴ * Q * U) = Uᴴ * (P * Q) * U := by
    intro P Q
    calc (Uᴴ * P * U) * (Uᴴ * Q * U) = Uᴴ * P * (U * Uᴴ) * Q * U := by
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * (P * Q) * U := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have back : ∀ P : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * P * U) * Uᴴ = P := by
    intro P
    calc U * (Uᴴ * P * U) * Uᴴ = (U * Uᴴ) * P * (U * Uᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = P := by rw [h2]; simp
  have hcomm : (Uᴴ * H * U) * (Uᴴ * Y * U) = (Uᴴ * Y * U) * (Uᴴ * H * U) := by
    rw [conj_mul, conj_mul, hHY]
  have hdH : Matrix.diagonal (fun i => (Uᴴ * H * U) i i) = Uᴴ * H * U := hH.diagonal_diag
  have hdA : Matrix.diagonal (fun i => (Uᴴ * A * U) i i) = Uᴴ * A * U := hA.diagonal_diag
  have key := commute_diagonal_of_dominated (fun i => (Uᴴ * H * U) i i)
    (fun i => (Uᴴ * A * U) i i) (Uᴴ * Y * U) (by rw [hdH]; exact hcomm) hdom
  rw [hdA, conj_mul, conj_mul] at key
  have := congrArg (fun M => U * M * Uᴴ) key
  simpa only [back] using this

end GlobalTheory.CompanionTheory.MatrixComm
