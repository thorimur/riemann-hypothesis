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
import Mathlib.RingTheory.PiTensorProduct
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
open Module

namespace GlobalTheory

theorem card_quot_span_pow_succ_eq_mul_domain (O : Type) [CommRing O] [IsDomain O] (t : O) (ht : t ≠ 0)
    (r : ℕ) :
    Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) =
      Nat.card (O ⧸ Ideal.span {t}) * Nat.card (O ⧸ Ideal.span {t ^ r}) := by
  set H := (Ideal.span {t ^ (r + 1)}).toAddSubgroup with hH
  set K := (Ideal.span {t ^ r}).toAddSubgroup with hK
  have hHK : H ≤ K := by
    intro x hx
    simp only [hH, hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx ⊢
    exact (pow_dvd_pow t (Nat.le_succ r)).trans hx
  have e1 : Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) = H.index := rfl
  have e2 : Nat.card (O ⧸ Ideal.span {t ^ r}) = K.index := rfl
  have e3 : Nat.card (O ⧸ Ideal.span {t}) = (Ideal.span {t}).toAddSubgroup.index := rfl
  rw [e1, e2, e3, ← AddSubgroup.relIndex_mul_index hHK]
  congr 1
  let φ : O →+ K :=
    { toFun := fun x => ⟨t ^ r * x, by
        simp only [hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
        exact dvd_mul_right _ _⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [mul_add] }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span {t ^ r} := hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    exact ⟨a, rfl⟩
  have hc : (H.addSubgroupOf K).comap φ = (Ideal.span {t}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH,
      Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    change t ^ (r + 1) ∣ t ^ r * x ↔ t ∣ x
    rw [pow_succ]
    exact mul_dvd_mul_iff_left (pow_ne_zero r ht)
  rw [AddSubgroup.relIndex, ← hc, AddSubgroup.index_comap_of_surjective _ hφ]

theorem card_quot_span_pow :
    ∀ (O : Type) [CommRing O] [IsDomain O] (t : O), t ≠ 0 → Finite (O ⧸ Ideal.span {t}) →
      ∀ r : ℕ, Nat.card (O ⧸ Ideal.span {t ^ r}) = Nat.card (O ⧸ Ideal.span {t}) ^ r := by
  intro O _ _ t ht _ r
  induction r with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ r ih =>
    rw [card_quot_span_pow_succ_eq_mul_domain O t ht r, ih, pow_succ, mul_comm]

end GlobalTheory
