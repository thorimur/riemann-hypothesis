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
import Mathlib.Tactic.Monotonicity.Lemmas
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

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_le_of_exact {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : LinearMap.ker g ≤ LinearMap.range f) :
    Module.length R B ≤ Module.length R C + Module.length R A := by
  have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  rw [e, add_comm]
  refine add_le_add (Module.length_le_of_injective _ (Submodule.subtype_injective _)) ?_
  exact (Module.length_le_of_injective _ (Submodule.inclusion_injective h)).trans
    (Module.length_le_of_surjective _ f.surjective_rangeRestrict)

theorem UpperTheory.V.Base.lenComp :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N] (a b : Module.End R N),
      Module.length R (LinearMap.ker (a * b)) ≤ Module.length R (LinearMap.ker a) + Module.length R (LinearMap.ker b) ∧
      Module.length R (N ⧸ LinearMap.range (a * b)) ≤ Module.length R (N ⧸ LinearMap.range a) + Module.length R (N ⧸ LinearMap.range b) := by
  intro R N _ _ _ a b
  constructor
  · have h1 : LinearMap.ker b ≤ LinearMap.ker (a * b) := fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [Module.End.mul_apply, hx, map_zero]
    have h2 : ∀ x ∈ LinearMap.ker (a * b), b x ∈ LinearMap.ker a := fun x hx => hx
    refine length_le_of_exact (Submodule.inclusion h1) (LinearMap.restrict b h2) fun x hx => ?_
    exact ⟨⟨x.1, congrArg Subtype.val hx⟩, rfl⟩
  · have h1 : LinearMap.range b ≤ (LinearMap.range (a * b)).comap a := by
      rintro _ ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    have h2 : LinearMap.range (a * b) ≤ (LinearMap.range a).comap LinearMap.id := by
      rintro _ ⟨y, rfl⟩
      exact ⟨b y, rfl⟩
    refine length_le_of_exact (Submodule.mapQ _ _ a h1) (Submodule.mapQ _ _ LinearMap.id h2) fun x hx => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [Submodule.mapQ_apply, hy]
    rfl
