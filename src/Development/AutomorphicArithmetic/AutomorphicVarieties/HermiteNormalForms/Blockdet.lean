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

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.blockdet :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (E : Matrix ι ι ℂ) (A : ι → Matrix (Fin N) (Fin N) ℂ),
    (Matrix.of fun s t : Fin N × ι => ∑ φ, star (E φ s.2) * A φ s.1 t.1 * E φ t.2).det =
      (star E.det * E.det) ^ N * ∏ φ, (A φ).det := by
  intro ι _ _ N E A
  have key : (Matrix.of fun s t : Fin N × ι => ∑ φ, star (E φ s.2) * A φ s.1 t.1 * E φ t.2) =
      (Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) E)ᴴ * Matrix.blockDiagonal A *
        Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) E := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Matrix.blockDiagonal_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, ite_mul, mul_ite, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.kronecker,
    Matrix.det_kronecker, Matrix.det_blockDiagonal]
  simp [star_pow, mul_pow]
  ring
