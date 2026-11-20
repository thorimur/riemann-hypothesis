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
import Mathlib.Topology.Sheaves.Presheaf

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.comap_pow_le :
    ∀ {A M M' : Type} [CommRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M'] [Module.Finite A M'] (I : Ideal A) (f : M →ₗ[A] M'), ∃ c : ℕ, ∀ m : ℕ, (I ^ (m + c) • (⊤ : Submodule A M')).comap f ≤ LinearMap.ker f ⊔ I ^ m • (⊤ : Submodule A M) := by
  intro A M M' _ _ _ _ _ _ _ I f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range f)
  refine ⟨k, fun m x hx => ?_⟩
  have h1 : f x ∈ I ^ (m + k) • (⊤ : Submodule A M') ⊓ LinearMap.range f :=
    ⟨hx, LinearMap.mem_range_self f x⟩
  rw [hk (m + k) (Nat.le_add_left k m), Nat.add_sub_cancel] at h1
  have h2 : f x ∈ I ^ m • LinearMap.range f :=
    Submodule.smul_mono le_rfl inf_le_right h1
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h2
  have h3 : x ∈ ((I ^ m • (⊤ : Submodule A M)).map f).comap f := h2
  rw [Submodule.comap_map_eq, sup_comm] at h3
  exact h3
