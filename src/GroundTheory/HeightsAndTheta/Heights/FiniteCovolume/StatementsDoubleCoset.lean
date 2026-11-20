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
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

section Slice

variable {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] [TopologicalSpace G]
  [TopologicalSpace G₁] [TopologicalSpace G₂]

def sliceGroup (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) (K : Subgroup G₂) (s : G₂) : Subgroup G₁ :=
  (Γ ⊓ (Subgroup.prod ⊤ (K.map (MulAut.conj s).toMonoidHom)).comap
      Φ.toMulEquiv.toMonoidHom).map ((MonoidHom.fst G₁ G₂).comp Φ.toMulEquiv.toMonoidHom)

theorem mem_sliceGroup {Φ : G ≃ₜ* G₁ × G₂} {Γ : Subgroup G} {K : Subgroup G₂} {s : G₂} {x : G₁} :
    x ∈ sliceGroup Φ Γ K s ↔ ∃ γ ∈ Γ, s⁻¹ * (Φ γ).2 * s ∈ K ∧ (Φ γ).1 = x := by
  simp only [sliceGroup, Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_comap,
    Subgroup.mem_prod, Subgroup.mem_top, true_and, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_fst]
  constructor
  · rintro ⟨γ, ⟨hγ, k, hk, hks⟩, rfl⟩
    refine ⟨γ, hγ, ?_, rfl⟩
    have : (Φ γ).2 = s * k * s⁻¹ := by
      have := hks.symm
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] at this
      exact this
    rw [this]
    simpa [mul_assoc] using hk
  · rintro ⟨γ, hγ, hk, rfl⟩
    refine ⟨γ, ⟨hγ, s⁻¹ * (Φ γ).2 * s, hk, ?_⟩, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, mul_assoc,
      mul_inv_cancel, mul_one, mul_inv_cancel_left]
    rfl

end Slice

def DoubleCosetCovolume.Statement (G G₁ G₂ : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] :
    Prop :=
  ∀ (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) [Countable Γ] (K : Subgroup G₂) (S : Finset G₂),
    IsCompact (K : Set G₂) → IsOpen (K : Set G₂) →
    (∀ γ ∈ Γ, (Φ γ).1 = 1 → γ = 1) →
    (∀ y : G₂, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, y = (Φ γ).2 * s * k) →
    (∀ s ∈ S, ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure], ∃ FD₁ : Set G₁,
      IsFundamentalDomain (sliceGroup Φ Γ K s) FD₁ μ₁ ∧ μ₁ FD₁ < ⊤) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure], ∃ FD : Set G, IsFundamentalDomain Γ FD μ ∧ μ FD < ⊤

section Inhabitants

abbrev C3 : Type := Multiplicative (ZMod 3)

instance : MeasurableSpace C3 := borel C3

instance : BorelSpace C3 := ⟨rfl⟩

def isHyperbolicPair_isotropic_dual : Subgroup (C3 × C3) := (MonoidHom.prod (MonoidHom.id C3) (MonoidHom.id C3)).range

theorem DoubleCosetCovolume.hypotheses_met :
    ∃ (Φ : C3 × C3 ≃ₜ* C3 × C3) (Γ : Subgroup (C3 × C3)) (_ : Countable Γ) (K : Subgroup C3)
      (S : Finset C3), Γ ≠ ⊥ ∧ IsCompact (K : Set C3) ∧ IsOpen (K : Set C3) ∧
      (∀ γ ∈ Γ, (Φ γ).1 = 1 → γ = 1) ∧
      (∀ y : C3, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, y = (Φ γ).2 * s * k) ∧
      (∀ s ∈ S, ∀ (μ₁ : Measure C3) [μ₁.IsHaarMeasure], ∃ FD₁ : Set C3,
        IsFundamentalDomain (sliceGroup Φ Γ K s) FD₁ μ₁ ∧ μ₁ FD₁ < ⊤) := by
  refine ⟨ContinuousMulEquiv.refl _, isHyperbolicPair_isotropic_dual, inferInstance, ⊥, {1}, ?_,
    (Set.finite_singleton 1).isCompact, isOpen_discrete _, ?_, ?_, ?_⟩
  · intro h
    have : ((Multiplicative.ofAdd (1 : ZMod 3), Multiplicative.ofAdd (1 : ZMod 3)) : C3 × C3) ∈
        isHyperbolicPair_isotropic_dual := ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact absurd (congrArg Prod.fst this) (by decide)
  · rintro γ ⟨a, rfl⟩ h1
    simp only [ContinuousMulEquiv.refl_apply, MonoidHom.prod_apply, MonoidHom.id_apply] at h1 ⊢
    simp [h1]
  · intro y
    exact ⟨(y, y), ⟨y, rfl⟩, 1, Finset.mem_singleton_self 1, 1, Subgroup.one_mem _, by simp⟩
  · intro s hs μ₁ _
    rw [Finset.mem_singleton] at hs
    subst hs
    have hbot : sliceGroup (ContinuousMulEquiv.refl (C3 × C3)) isHyperbolicPair_isotropic_dual ⊥ 1 = ⊥ := by
      ext x
      rw [mem_sliceGroup, Subgroup.mem_bot]
      constructor
      · rintro ⟨γ, ⟨a, rfl⟩, hk, rfl⟩
        simp only [ContinuousMulEquiv.refl_apply, MonoidHom.prod_apply, MonoidHom.id_apply,
          inv_one, one_mul, mul_one, Subgroup.mem_bot] at hk ⊢
        exact hk
      · rintro rfl
        exact ⟨1, Subgroup.one_mem _, by simp, by simp⟩
    refine ⟨Set.univ, ?_, isCompact_univ.measure_lt_top⟩
    rw [hbot]
    exact IsFundamentalDomain.mk' MeasurableSet.univ.nullMeasurableSet fun x =>
      ⟨1, Set.mem_univ _, fun γ _ => Subsingleton.elim _ _⟩

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
