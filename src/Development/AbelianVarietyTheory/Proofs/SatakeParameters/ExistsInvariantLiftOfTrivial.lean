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
import Mathlib.Topology.Sheaves.Init
open GlobalTheory.Cong

namespace GlobalTheory

theorem exists_leftInv_rightEquivariant (G A : Type) [Group G] [AddCommGroup A] (Γ C : Subgroup G)
    (lam : C →* Multiplicative A)
    (h : ∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) :
    ∃ ℓ : G → A, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧
      ∀ g (c : C), ℓ (g * c) = ℓ g + Multiplicative.toAdd (lam c) := by

  have key : ∀ (s γ γ' : G), γ ∈ Γ → γ' ∈ Γ → ∀ c c' : C,
      γ * s * c = γ' * s * c' → lam c = lam c' := by
    intro s γ γ' hγ hγ' c c' e
    have e2 : (γ'⁻¹ * γ) * s = s * ((c' * c⁻¹ : C) : G) := by
      push_cast
      calc γ'⁻¹ * γ * s = γ'⁻¹ * (γ * s * c) * (c : G)⁻¹ := by group
        _ = γ'⁻¹ * (γ' * s * c') * (c : G)⁻¹ := by rw [e]
        _ = s * ((c' : G) * (c : G)⁻¹) := by group
    have := h s _ (Γ.mul_mem (Γ.inv_mem hγ') hγ) _ e2
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this.symm
  let S : Setoid G :=
    { r := fun a b => ∃ γ ∈ Γ, ∃ c : C, b = γ * a * c
      iseqv := by
        refine ⟨fun a => ⟨1, Γ.one_mem, 1, by simp⟩, ?_, ?_⟩
        · rintro a b ⟨γ, hγ, c, rfl⟩
          exact ⟨γ⁻¹, Γ.inv_mem hγ, c⁻¹, by push_cast; group⟩
        · rintro a b d ⟨γ, hγ, c, rfl⟩ ⟨γ', hγ', c', rfl⟩
          exact ⟨γ' * γ, Γ.mul_mem hγ' hγ, c * c', by push_cast; group⟩ }
  let rep : G → G := fun g => (Quotient.mk S g).out
  have hrep : ∀ g, ∃ c : C, ∃ γ ∈ Γ, g = γ * rep g * c := by
    intro g
    obtain ⟨γ, hγ, c, e⟩ := Quotient.mk_out (s := S) g
    exact ⟨c, γ, hγ, e⟩
  have rep_eq : ∀ a b, S.r a b → rep a = rep b := by
    intro a b hab
    simp only [rep]
    rw [Quotient.sound hab]
  let cf : G → C := fun g => Classical.choose (hrep g)
  have hcf : ∀ g, ∃ γ ∈ Γ, g = γ * rep g * cf g := fun g => Classical.choose_spec (hrep g)
  refine ⟨fun g => Multiplicative.toAdd (lam (cf g)), ?_, ?_⟩
  · intro γ hγ g
    simp only
    congr 1
    have hr : rep (γ * g) = rep g := (rep_eq _ _ ⟨γ, hγ, 1, by simp⟩).symm
    obtain ⟨γ1, hγ1, e1⟩ := hcf (γ * g)
    obtain ⟨γ2, hγ2, e2⟩ := hcf g
    rw [hr] at e1
    apply key (rep g) (γ⁻¹ * γ1) γ2 (Γ.mul_mem (Γ.inv_mem hγ) hγ1) hγ2
    calc γ⁻¹ * γ1 * rep g * (cf (γ * g) : G) = γ⁻¹ * (γ1 * rep g * cf (γ * g)) := by group
      _ = g := by rw [← e1]; group
      _ = γ2 * rep g * cf g := e2
  · intro g c
    simp only
    rw [← toAdd_mul]
    congr 1
    have hr : rep (g * c) = rep g := (rep_eq _ _ ⟨1, Γ.one_mem, c, by simp⟩).symm
    obtain ⟨γ1, hγ1, e1⟩ := hcf (g * c)
    obtain ⟨γ2, hγ2, e2⟩ := hcf g
    rw [hr] at e1
    have := key (rep g) γ1 γ2 hγ1 hγ2 (cf (g * c) * c⁻¹) (cf g) (by
      push_cast
      calc γ1 * rep g * ((cf (g * c) : G) * (c : G)⁻¹) = (γ1 * rep g * cf (g * c)) * (c : G)⁻¹ := by group
        _ = g := by rw [← e1]; group
        _ = γ2 * rep g * cf g := e2)
    rw [map_mul, map_inv] at this
    rw [← this]; group

example : ∀ (G A : Type) [Group G] [AddCommGroup A] (Γ C : Subgroup G) (lam : C →* Multiplicative A), (∀ g : G, ∀ γ ∈ Γ, ∀ c : C, γ * g = g * c → lam c = 1) → ∃ ℓ : G → A, (∀ γ ∈ Γ, ∀ g, ℓ (γ * g) = ℓ g) ∧ ∀ g (c : C), ℓ (g * c) = ℓ g + Multiplicative.toAdd (lam c) := exists_leftInv_rightEquivariant

end GlobalTheory
