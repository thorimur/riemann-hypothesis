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
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem dlog_ratio_det {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  intro g
  set u : Fin (n + 1) → R := fun j => (((t j)⁻¹ : Rˣ) : R) with hu
  have htu : ∀ j, (t j : R) * u j = 1 := fun j => by simp [hu]
  have hDu : ∀ k j, D k (u j) = if k = j then -(u j * u j) else 0 := by
    intro k j
    have h2 := (D k).leibniz_of_mul_eq_one (a := u j) (b := (t j : R)) (by rw [mul_comm]; exact htu j)
    rw [h2, hD k j]
    split_ifs <;> simp [pow_two]
  have hg0 : g 0 = u 0 := by simp [g, hu]
  have hgs : ∀ (l : Fin (n + 1)) (h : (l : ℕ) ≠ 0), g l = (t ⟨l - 1, by omega⟩ : R) * u l := by
    intro l h
    exact dif_neg h
  have hgu : ∀ l, IsUnit (g l) := by
    intro l
    by_cases h : (l : ℕ) = 0
    · simp only [g, h, dite_true]; exact Units.isUnit _
    · simp only [g, h, dite_false]; exact (Units.isUnit _).mul (Units.isUnit _)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of fun k l => if k = l then -1 else if (k : ℕ) + 1 = l then 1 else 0
  have hM : (Matrix.of fun k l => D k (g l)) = Matrix.diagonal u * B * Matrix.diagonal g := by
    ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, B]
    by_cases h : (l : ℕ) = 0
    · have hl : l = 0 := Fin.ext h
      subst hl
      have hk : ¬ ((k : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ)) := by simp
      rw [hg0, hDu k 0]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]
    · rw [hgs l h, Derivation.leibniz, hDu k l, hD k _]
      simp only [smul_eq_mul]
      by_cases hkl : k = l
      · subst hkl
        have hne : k ≠ ⟨(k : ℕ) - 1, by omega⟩ := by
          intro e
          have := congrArg Fin.val e
          simp at this
          omega
        simp only [if_true, hne, if_false]
        ring
      · by_cases hs : (k : ℕ) + 1 = l
        · have hp : k = ⟨(l : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [if_neg hkl, if_pos hp, if_neg hkl, if_pos hs, ← hp]
          have := htu k
          linear_combination (-(u l)) * this
        · have hp : k ≠ ⟨(l : ℕ) - 1, by omega⟩ := by
            intro e
            have := congrArg Fin.val e
            simp at this
            omega
          rw [if_neg hkl, if_neg hp, if_neg hkl, if_neg hs]
          simp
  have hB : B.det = (-1) ^ (n + 1) := by
    rw [Matrix.det_of_upperTriangular]
    · simp [B]
    · intro i j hij
      have : (j : ℕ) < i := hij
      have h1 : i ≠ j := fun h => by simp [h] at this
      have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
      simp [B, h1, h2]
  have hprod : ∏ k, u k = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    simp only [hu, ← Units.coe_prod, Finset.prod_inv_distrib]
  have hU : IsUnit (∏ k, g k) := by
    obtain ⟨v, hv⟩ := IsUnit.prod_univ_iff.2 hgu
    exact hv ▸ v.isUnit
  have hcan : Ring.inverse (∏ k, g k) * (∏ k, g k) = 1 := Ring.inverse_mul_cancel _ hU
  have key : Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det =
      (-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, hprod]
    linear_combination ((-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R)) * hcan
  rcases neg_one_pow_eq_or R (n + 1) with h | h
  · left; rw [key, h, one_mul]
  · right; rw [key, h, neg_one_mul]

end GlobalTheory.CompanionTheory.Cone
