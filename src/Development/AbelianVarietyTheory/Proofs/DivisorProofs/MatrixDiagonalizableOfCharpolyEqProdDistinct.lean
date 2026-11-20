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
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
open Polynomial

namespace GlobalTheory

theorem matrix_diagonalizable_of_charpoly_eq_prod_distinct (K : Type) [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (ν : Fin n → K) (hν : Function.Injective ν)
    (hγ : γ.charpoly = ∏ k, (X - C (ν k))) :
    ∃ y : GL (Fin n) K, γ * (y : Matrix (Fin n) (Fin n) K) = (y : Matrix (Fin n) (Fin n) K) * Matrix.diagonal ν := by
  have hev : ∀ k, Module.End.HasEigenvalue (Matrix.toLin' γ) (ν k) := by
    intro k
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hγ]
    simp only [IsRoot, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)
  choose v hv using fun k => (hev k).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ ν hν v hv
  set Y : Matrix (Fin n) (Fin n) K := Matrix.of fun i k => v k i with hY
  have hcols : Y.col = v := by
    funext k i; rfl
  have hu : IsUnit Y := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    rw [hcols]; exact hli
  refine ⟨hu.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  ext i k
  rw [Matrix.mul_diagonal]
  have h1 := (hv k).apply_eq_smul
  rw [Matrix.toLin'_apply] at h1
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  rw [Matrix.mul_apply]
  simp only [hY, Matrix.of_apply]
  rw [mul_comm, ← h2]
  rfl

end GlobalTheory
