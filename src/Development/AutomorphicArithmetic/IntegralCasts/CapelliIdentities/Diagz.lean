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

theorem UpperTheory.Reformulated.B.Qh2.diagz :
    ∀ {K : Type} [inst : Field K]
    (M : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) (a : Fin (4 : ℕ) → K),
    Function.Injective a →
      M.charpoly = ∏ i : Fin (4 : ℕ), (Polynomial.X - (Polynomial.C : K → Polynomial K) (a i)) →
        ∃ (P : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) (Q : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K),
          P * Q = (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) ∧
            Q * P = (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) K) ∧ Q * M * P = Matrix.diagonal a := by
  intro K _ M a ha hM
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) a ha v hv
  let P : Matrix (Fin 4) (Fin 4) K := Matrix.of fun r c => v c r
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hMP : M * P = P * Matrix.diagonal a := by
    ext r c
    have h := congrFun (hv c).apply_eq_smul r
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    exact h
  refine ⟨P, P⁻¹, Matrix.mul_nonsing_inv P hdet, Matrix.nonsing_inv_mul P hdet, ?_⟩
  rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul]
