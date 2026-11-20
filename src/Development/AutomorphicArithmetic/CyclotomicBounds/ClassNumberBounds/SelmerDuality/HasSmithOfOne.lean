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
import Std.Tactic.BVDecide.Normalize.Prop

namespace KStar.Selmer

open Matrix Module

variable {R : Type*} [CommRing R]

private def HasSmith {a : ℕ} (Φ : Matrix (Fin a) (Fin a) R) : Prop :=
  ∃ (U V : Matrix (Fin a) (Fin a) R) (d : Fin a → R), IsUnit U.det ∧ IsUnit V.det ∧
      Φ = U * diagonal d * V ∧ ∀ i j, i ≤ j → d i ∣ d j

private theorem HasSmith.smul {a : ℕ} {Φ : Matrix (Fin a) (Fin a) R} (h : HasSmith Φ) (x : R) :
    HasSmith (x • Φ) := by
  obtain ⟨U, V, d, hU, hV, rfl, hd⟩ := h
  refine ⟨U, V, x • d, hU, hV, ?_, fun i j hij => ?_⟩
  · rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]
  · exact mul_dvd_mul_left x (hd i j hij)

private theorem HasSmith.perm {a : ℕ} {Φ : Matrix (Fin a) (Fin a) R} (h : HasSmith Φ)
    (σ τ : Equiv.Perm (Fin a)) : HasSmith (Φ.submatrix σ τ) := by
  obtain ⟨U, V, d, hU, hV, rfl, hd⟩ := h
  refine ⟨U.submatrix σ id, V.submatrix id τ, d, ?_, ?_, ?_, hd⟩
  · rw [det_permute]
    exact ((Equiv.Perm.sign σ).isUnit.map (Int.castRingHom R)).mul hU
  · rw [det_permute']
    exact ((Equiv.Perm.sign τ).isUnit.map (Int.castRingHom R)).mul hV
  · ext i j
    simp [Matrix.mul_apply]

private def consEquiv (a : ℕ) : Fin (a + 1) ≃ Unit ⊕ Fin a where
  toFun := Fin.cases (Sum.inl ()) Sum.inr
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by cases i using Fin.cases <;> simp
  right_inv i := by rcases i with _ | i <;> simp

private theorem hasSmith_of_one {a : ℕ} (ih : ∀ Ψ : Matrix (Fin a) (Fin a) R, HasSmith Ψ)
    (M : Matrix (Fin (a + 1)) (Fin (a + 1)) R) (h : M 0 0 = 1) : HasSmith M := by
  set e := consEquiv a with he
  set N := M.submatrix e.symm e.symm with hN
  have h11 : N.toBlocks₁₁ = 1 := by
    ext i j
    have : N (Sum.inl i) (Sum.inl j) = M 0 0 := rfl
    simp [toBlocks₁₁, this, h]
  obtain ⟨U, V, d, hU, hV, hΨ, hd⟩ := ih (N.toBlocks₂₂ - N.toBlocks₂₁ * N.toBlocks₁₂)
  have key : N = fromBlocks 1 0 N.toBlocks₂₁ U * diagonal (Sum.elim (fun _ => 1) d) *
      fromBlocks 1 N.toBlocks₁₂ 0 V := by
    rw [← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply]
    conv_lhs => rw [← fromBlocks_toBlocks N, h11]
    simp [← hΨ]
  refine ⟨(fromBlocks 1 0 N.toBlocks₂₁ U).submatrix e e,
    (fromBlocks 1 N.toBlocks₁₂ 0 V).submatrix e e, Sum.elim (fun _ => 1) d ∘ e, ?_, ?_, ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; simpa using hU
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁]; simpa using hV
  · rw [← submatrix_diagonal_equiv, submatrix_mul_equiv, submatrix_mul_equiv, ← key, hN]
    simp
  · intro i j hij
    cases i using Fin.cases with
    | zero => exact one_dvd _
    | succ i =>
      cases j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j => exact hd i j (by simpa using hij)

private theorem exists_dvd_all [PreValuationRing R] {ι : Type*} (f : ι → R) (s : Finset ι)
    (hs : s.Nonempty) : ∃ p ∈ s, ∀ i ∈ s, f p ∣ f i := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, by simp, by simp⟩
  | cons a s ha hs ih =>
    obtain ⟨p, hp, h⟩ := ih
    obtain ⟨c, hc | hc⟩ := PreValuationRing.cond (f a) (f p)
    · refine ⟨a, by simp, fun i hi => ?_⟩
      rcases Finset.mem_cons.1 hi with rfl | hi
      · exact dvd_rfl
      · exact (Dvd.intro c hc).trans (h i hi)
    · refine ⟨p, by simp [hp], fun i hi => ?_⟩
      rcases Finset.mem_cons.1 hi with rfl | hi
      · exact Dvd.intro c hc
      · exact h i hi

private theorem hasSmith_all [PreValuationRing R] (a : ℕ) (Φ : Matrix (Fin a) (Fin a) R) :
    HasSmith Φ := by
  classical
  induction a with
  | zero =>
    exact ⟨1, 1, fun _ => 1, by simp, by simp, Subsingleton.elim _ _, fun _ _ _ => dvd_rfl⟩
  | succ a ih =>
    obtain ⟨⟨p, q⟩, -, h⟩ := exists_dvd_all (fun ij : Fin (a + 1) × Fin (a + 1) => Φ ij.1 ij.2)
      Finset.univ Finset.univ_nonempty
    have h' : ∀ i j, ∃ c, Φ i j = Φ p q * c ∧ (i = p → j = q → c = 1) := by
      intro i j
      by_cases hij : i = p ∧ j = q
      · obtain ⟨rfl, rfl⟩ := hij
        exact ⟨1, by simp, by simp⟩
      · obtain ⟨c, hc⟩ := h (i, j) (Finset.mem_univ _)
        exact ⟨c, hc, fun h1 h2 => absurd ⟨h1, h2⟩ hij⟩
    choose M hM hM1 using h'
    have h1 : HasSmith ((Matrix.of M).submatrix (Equiv.swap 0 p) (Equiv.swap 0 q)) :=
      hasSmith_of_one ih _ (by simp [hM1 p q rfl rfl])
    have h2 := (h1.perm (Equiv.swap 0 p) (Equiv.swap 0 q)).smul (Φ p q)
    convert h2 using 1
    ext i j
    simpa using hM i j

theorem exists_smith [PreValuationRing R] (a : ℕ) (Φ : Matrix (Fin a) (Fin a) R) :
    ∃ (U V : Matrix (Fin a) (Fin a) R) (d : Fin a → R), IsUnit U.det ∧ IsUnit V.det ∧
      Φ = U * diagonal d * V ∧ ∀ i j, i ≤ j → d i ∣ d j :=
  hasSmith_all a Φ

end KStar.Selmer
