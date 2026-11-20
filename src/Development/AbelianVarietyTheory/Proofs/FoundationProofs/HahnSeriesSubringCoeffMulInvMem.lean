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
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HahnSub

theorem coeff_mul_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h h' : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hh' : ∀ r, h'.coeff r ∈ A) (r : ℚ) : (h * h').coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact A.sum_mem fun ij _ => A.mul_mem (hh ij.1) (hh' ij.2)

theorem coeff_inv_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hl : h.leadingCoeff⁻¹ ∈ A) (r : ℚ) : (h⁻¹).coeff r ∈ A := by
  by_cases h0 : h = 0
  · subst h0
    simp

  let g : HahnSeries ℚ A :=
    { coeff := fun s => ⟨h.coeff s, hh s⟩
      isPWO_support' := h.isPWO_support.mono fun s hs e => hs (Subtype.ext e) }
  have hg : ∀ s, (g.coeff s : Ω) = h.coeff s := fun s => rfl
  have hg0 : g ≠ 0 := by
    intro e
    apply h0
    ext s
    rw [← hg, e]
    rfl
  have hord : g.order = h.order := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 h0
      rw [HahnSeries.leadingCoeff_eq, ← hg, e]
      rfl
    · apply HahnSeries.order_le_of_coeff_ne_zero
      rw [← hg]
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 hg0
      rw [HahnSeries.leadingCoeff_eq]
      exact Subtype.ext e
  have hlead : (g.leadingCoeff : Ω) = h.leadingCoeff := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hg, hord]
  have hunit : IsUnit g.leadingCoeff := by
    refine IsUnit.of_mul_eq_one (⟨h.leadingCoeff⁻¹, hl⟩ : A) ?_
    apply Subtype.ext
    show (g.leadingCoeff : Ω) * h.leadingCoeff⁻¹ = 1
    rw [hlead]
    exact mul_inv_cancel₀ (HahnSeries.leadingCoeff_ne_zero.2 h0)
  obtain ⟨v, hv⟩ := (HahnSeries.isUnit_iff.2 hunit).exists_right_inv
  let f : A →ₙ+* Ω := A.subtype.toNonUnitalRingHom
  have hgf : g.map f = h := by
    ext s
    rfl
  have hone : (1 : HahnSeries ℚ A).map f = 1 := by
    ext s
    rw [HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> rfl
  have key : h * v.map f = 1 := by
    rw [← hgf, ← HahnSeries.map_mul, hv, hone]
  rw [inv_eq_of_mul_eq_one_right key, HahnSeries.map_coeff]
  exact (v.coeff r).2

theorem coeff_mul_inv_mem : ∀ (Ω : Type) [Field Ω] (A : Subring Ω), (∀ h h' : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → (∀ r, h'.coeff r ∈ A) → ∀ r, (h * h').coeff r ∈ A) ∧ ∀ h : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → h.leadingCoeff⁻¹ ∈ A → ∀ r, (h⁻¹).coeff r ∈ A := by
  intro Ω _ A
  exact ⟨fun h h' hh hh' r => coeff_mul_mem A h h' hh hh' r,
    fun h hh hl r => coeff_inv_mem A h hh hl r⟩

end GlobalTheory.HahnSub
