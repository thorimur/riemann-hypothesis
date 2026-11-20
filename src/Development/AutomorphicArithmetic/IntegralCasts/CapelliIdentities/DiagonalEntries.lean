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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.DiagonalizeTwoByTwo.diagE :
    ∀ {κ : Type} [inst : Field κ]
    (M : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) (α : Fin (2 : ℕ) → κ),
    Function.Injective α →
      M.charpoly = ∏ i : Fin (2 : ℕ), (Polynomial.X - (Polynomial.C : κ → Polynomial κ) (α i)) →
        ∃ (P : GL (Fin (2 : ℕ)) κ),
          M * (↑P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) =
            (↑P : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) κ) * Matrix.diagonal α := by
  intro κ _ M α hα h
  classical
  have hv : ∀ i : Fin 2, ∃ v : Fin 2 → κ, v ≠ 0 ∧ M.mulVec v = α i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin 2) (α i) - M).det = 0 := by
      rw [← Matrix.eval_charpoly, h, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.mulVec_diagonal]
  choose v hv0 hv using hv
  have hli : LinearIndependent κ v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) α hα v fun i =>
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hv i), hv0 i⟩
  have hu : IsUnit (Matrix.of v).transpose :=
    Matrix.linearIndependent_cols_iff_isUnit.1 hli
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  ext j i
  have := congrFun (hv i) j
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
