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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem _root_.UpperTheory.KN.exists_linearEquiv_quotient_of_lattice_sum :
    ∀ {O V A M : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup A] [Module O A] [AddCommGroup M] [Module O M]
      (j : A →ₗ[O] V) (q : A →ₗ[O] M) (B T₁ T₂ : Submodule O V), Function.Injective j → Function.Surjective q →
      (∀ a, j a ∈ B → q a = 0) → (∀ v, v ∈ T₁ ↔ ∃ a, ∃ b ∈ B, v = j a + b) → (∀ v, v ∈ T₂ ↔ ∃ a, q a = 0 ∧ ∃ b ∈ B, v = j a + b) →
      ∃ e : M ≃ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype), ∀ (a : A) (y : ↥T₁), e (q a) = Submodule.Quotient.mk y ↔ ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b := by
  intro O V A M _ _ _ _ _ _ _ j q B T₁ T₂ _ hq hB h1 h2
  have hj : ∀ a, j a ∈ T₁ := fun a => (h1 _).2 ⟨a, 0, B.zero_mem, by simp⟩
  let p : A →ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype) :=
    (T₂.comap T₁.subtype).mkQ ∘ₗ j.codRestrict T₁ hj
  have key : ∀ (a : A) (y : ↥T₁), p a = Submodule.Quotient.mk y ↔
      ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b := by
    intro a y
    have h : p a = Submodule.Quotient.mk y ↔ (y : V) - j a ∈ T₂ := by
      rw [eq_comm]
      exact Submodule.Quotient.eq (T₂.comap T₁.subtype)
    rw [h, h2]
    constructor
    · rintro ⟨a', ha', b, hb, hy⟩
      refine ⟨a' + a, by simp [ha'], b, hb, ?_⟩
      rw [map_add, add_right_comm, ← hy, sub_add_cancel]
    · rintro ⟨a', ha', b, hb, hy⟩
      refine ⟨a' - a, by simp [ha'], b, hb, ?_⟩
      rw [map_sub, hy]
      abel
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨a, b, hb, hy⟩ := (h1 _).1 y.2
    exact ⟨a, (key a y).2 ⟨a, rfl, b, hb, hy⟩⟩
  have hker : LinearMap.ker q = LinearMap.ker p := by
    ext a
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.Quotient.mk_zero, key]
    constructor
    · intro ha
      exact ⟨0, by simp [ha], 0, B.zero_mem, by simp⟩
    · rintro ⟨a', ha', b, hb, hy⟩
      rw [← ha']
      apply hB
      have : j a' = -b := eq_neg_of_add_eq_zero_left hy.symm
      rw [this]
      exact B.neg_mem hb
  refine ⟨(q.quotKerEquivOfSurjective hq).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (p.quotKerEquivOfSurjective hp)), fun a y => ?_⟩
  rw [← key]
  have h3 : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, h3]
  rfl
