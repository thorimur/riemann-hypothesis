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
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
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

theorem UpperTheory.Reformulated.B.ExistsDiagonalization.exists_diag :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (α : Fin n → K),
    Function.Injective α →
      P.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (α i)) →
        ∃ (V : Matrix (Fin n) (Fin n) K), IsUnit V ∧ P * V = V * Matrix.diagonal α := by
  intro K _ n P α hα hP
  have h1 : ∀ i, ∃ v : Fin n → K, v ≠ 0 ∧ P.mulVec v = α i • v := by
    intro i
    have h0 : P.charpoly.eval (α i) = 0 := by
      rw [hP, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [Matrix.eval_charpoly] at h0
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using h1
  have hli : LinearIndependent K v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' P) α hα v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa using hv i
  refine ⟨(Matrix.of v).transpose, ?_, ?_⟩
  · exact Matrix.linearIndependent_cols_iff_isUnit.mp hli
  · ext j i
    have h := congrFun (hv i) j
    rw [Matrix.mul_diagonal]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h
