import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

open Matrix Finset Real

namespace GlobalTheory

open scoped ComplexOrder in

theorem unipotent_isometry_definite_eq_one :
    ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ), c ≠ 0 → Aᴴ * (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * A = c • 1 → (A - 1) ^ m = 0 → A = 1 := by
  intro n m A c hc hA hm

  have hU : Aᴴ * A = 1 := by
    have h1 : c • (Aᴴ * A) = c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [← hA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    exact smul_right_injective _ hc h1
  have hU' : A * Aᴴ = 1 := mul_eq_one_comm.mp hU

  have hcomm : Commute (A - 1)ᴴ (A - 1) := by
    show (A - 1)ᴴ * (A - 1) = (A - 1) * (A - 1)ᴴ
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, sub_mul, mul_sub, hU, hU',
      one_mul, mul_one]
    abel
  have hN : (A - 1) ^ (m + 1) = 0 := by rw [pow_succ, hm, zero_mul]

  have hBh : ((A - 1)ᴴ * (A - 1))ᴴ = (A - 1)ᴴ * (A - 1) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hB : ((A - 1)ᴴ * (A - 1)) ^ (m + 1) = 0 := by
    rw [hcomm.mul_pow, hN, mul_zero]
  have key : ∀ k : ℕ, ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 → (A - 1)ᴴ * (A - 1) = 0 := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro hk
      apply ih
      have h2 : (((A - 1)ᴴ * (A - 1)) ^ (k + 1))ᴴ * ((A - 1)ᴴ * (A - 1)) ^ (k + 1) = 0 := by
        rw [Matrix.conjTranspose_pow, hBh, ← pow_add,
          show k + 1 + (k + 1) = (k + 1 + 1) + k by omega, pow_add, hk, zero_mul]
      exact Matrix.conjTranspose_mul_self_eq_zero.mp h2
  exact sub_eq_zero.mp (Matrix.conjTranspose_mul_self_eq_zero.mp (key m hB))

end GlobalTheory
