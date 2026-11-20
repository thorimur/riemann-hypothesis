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
import Mathlib.Topology.Sheaves.Init

open Matrix Finset

noncomputable section

namespace GenFrameSpan

theorem det_mul_rect {R : Type*} [CommRing R] {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply, Matrix.mul_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Matrix.submatrix_apply, id, Finset.smul_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Units.smul_def, zsmul_eq_mul]
  ring

theorem det_submatrix_fun {R : Type*} [CommRing R] {p n : ℕ} (M : Matrix (Fin p) (Fin n) R)
    (f : Fin p → Fin n) :
    (M.submatrix id f).det = 0 ∨ ∃ (J : Fin p ↪o Fin n) (e : ℤ),
      (M.submatrix id f).det = (e : R) * (M.submatrix id J).det := by
  classical
  by_cases hf : Function.Injective f
  · right
    set s := Finset.univ.image f with hs
    have hcard : s.card = p := by
      rw [hs, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    let J := s.orderEmbOfFin hcard
    have hmem : ∀ i, f i ∈ Set.range J := by
      intro i
      rw [Finset.range_orderEmbOfFin]
      simp [hs]
    choose g hg using hmem
    have hginj : Function.Injective g := by
      intro a b h
      apply hf
      rw [← hg a, ← hg b, h]
    let σ : Equiv.Perm (Fin p) := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj)
    refine ⟨J, (Equiv.Perm.sign σ : ℤ), ?_⟩
    have e : M.submatrix id f = (M.submatrix id J).submatrix id σ := by
      ext a b
      simp [σ, hg]
    rw [e, Matrix.det_permute']
    try norm_cast
  · left
    rw [Function.Injective] at hf
    push_neg at hf
    obtain ⟨i, j, hij, hne⟩ := hf
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hij])

end GenFrameSpan
