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
import Mathlib.Tactic.ENatToNat
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

noncomputable section
open Matrix

namespace PI.SqPair.LocCartanPairW

variable {R : Type*} [CommRing R] (σ : R ≃+* R)

theorem cmp_conjT_mul {l m n : Type*} [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    ((M * N).map σ)ᵀ = (N.map σ)ᵀ * (M.map σ)ᵀ := by
  ext i j
  simp only [transpose_apply, map_apply, mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem cmp_block_of_gram [IsDomain R] {μ κ : Type*} [Fintype μ] [Fintype κ] [DecidableEq μ]
    (M : Matrix (μ ⊕ κ) (μ ⊕ κ) R) (J : Matrix μ μ R) (A₁ A₁' : Matrix κ κ R) (s : R)
    (hM : (M.map σ)ᵀ * fromBlocks J 0 0 A₁ * M = s • fromBlocks J 0 0 A₁')
    (h21 : M.toBlocks₂₁ = 0)
    (hdet : (((M.toBlocks₁₁).map σ)ᵀ * J).det ≠ 0) :
    M.toBlocks₁₂ = 0 ∧ ((M.toBlocks₂₂).map σ)ᵀ * A₁ * M.toBlocks₂₂ = s • A₁' := by
  have hM' := hM
  rw [← Matrix.fromBlocks_toBlocks M, h21] at hM'
  simp only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul, Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, smul_zero] at hM'
  obtain ⟨-, h12', -, h22'⟩ := Matrix.fromBlocks_inj.1 hM'
  have hQ : M.toBlocks₁₂ = 0 := by
    have h1 : (((M.toBlocks₁₁).map σ)ᵀ * J).adjugate *
        (((M.toBlocks₁₁).map σ)ᵀ * J * M.toBlocks₁₂) = 0 := by
      rw [h12', Matrix.mul_zero]
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h1
    ext i j
    have hij := congrArg (fun X => X i j) h1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hij
    exact (mul_eq_zero.1 hij).resolve_left hdet
  refine ⟨hQ, ?_⟩
  rw [hQ] at h22'
  simpa using h22'

theorem cmp_det_diag_ne [IsDomain R] {μ : Type*} [Fintype μ] [DecidableEq μ] (J : Matrix μ μ R)
    (hJ : J.det ≠ 0) (c : μ → R) (hc : ∀ i, c i ≠ 0) :
    (((diagonal c).map σ)ᵀ * J).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.diagonal_map (map_zero σ), Matrix.det_diagonal]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => ?_) hJ
  intro h0
  exact hc i (σ.injective (by rw [h0, map_zero]))

theorem cmp_detJ [Nontrivial R] : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  simp

theorem cmp_block [IsDomain R] {ι μ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ]
    [DecidableEq μ] [Fintype κ] [DecidableEq κ]
    (A A' h : Matrix ι ι R) (s : R) (hh : (h.map σ)ᵀ * A * h = s • A')
    (J : Matrix μ μ R) (hJ : J.det ≠ 0) (A₁ A₁' : Matrix κ κ R)
    (u u' : Matrix ι (μ ⊕ κ) R) (v : Matrix (μ ⊕ κ) ι R) (hvu : v * u = 1) (huv : u * v = 1)
    (hG : (u.map σ)ᵀ * A * u = fromBlocks J 0 0 A₁)
    (hG' : (u'.map σ)ᵀ * A' * u' = fromBlocks J 0 0 A₁')
    (c : μ → R) (hc : ∀ i, c i ≠ 0)
    (hcol : ∀ r i, (h * u') r (Sum.inl i) = c i * u r (Sum.inl i)) :
    ∃ h₂ : Matrix κ κ R, v * h * u' = fromBlocks (diagonal c) 0 0 h₂ ∧
      (h₂.map σ)ᵀ * A₁ * h₂ = s • A₁' := by
  have hcolM : ∀ r i, (v * h * u') r (Sum.inl i) = (v * u) r (Sum.inl i) * c i := by
    intro r i
    rw [Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcol]
    ring
  rw [hvu] at hcolM
  have h11 : (v * h * u').toBlocks₁₁ = diagonal c := by
    ext a b
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hcolM, Matrix.one_apply, Sum.inl.injEq,
      diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  have h21 : (v * h * u').toBlocks₂₁ = 0 := by
    ext a b
    simp [Matrix.toBlocks₂₁, hcolM]
  have hu : u * (v * h * u') = h * u' := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, huv, Matrix.one_mul]
  have hgram : ((v * h * u').map σ)ᵀ * fromBlocks J 0 0 A₁ * (v * h * u') =
      s • fromBlocks J 0 0 A₁' := by
    rw [← hG, ← hG']
    calc ((v * h * u').map σ)ᵀ * ((u.map σ)ᵀ * A * u) * (v * h * u')
        = ((u * (v * h * u')).map σ)ᵀ * A * (u * (v * h * u')) := by
          rw [cmp_conjT_mul σ u (v * h * u')]
          simp only [Matrix.mul_assoc]
      _ = ((h * u').map σ)ᵀ * A * (h * u') := by rw [hu]
      _ = (u'.map σ)ᵀ * ((h.map σ)ᵀ * A * h) * u' := by
          rw [cmp_conjT_mul σ h u']
          simp only [Matrix.mul_assoc]
      _ = s • ((u'.map σ)ᵀ * A' * u') := by
          rw [hh, Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨h12, h22⟩ := cmp_block_of_gram σ (v * h * u') J A₁ A₁' s hgram h21
    (by rw [h11]; exact cmp_det_diag_ne σ J hJ c hc)
  refine ⟨(v * h * u').toBlocks₂₂, ?_, h22⟩
  rw [← h11, ← h12, ← h21]
  exact (Matrix.fromBlocks_toBlocks _).symm

end PI.SqPair.LocCartanPairW
