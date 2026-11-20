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
import Mathlib.RingTheory.PowerSeries.Basic
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

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

variable {A B R : Type} [CommRing A] [CommRing B] [CommRing R]

def IsRingHomMod (π : B →+* A) (β : B →+* R) (n : ℕ) (φ : A → PowerSeries R) : Prop :=
  (∀ f g, (X : PowerSeries R) ^ n ∣ φ (f * g) - φ f * φ g) ∧
  (∀ f g, (X : PowerSeries R) ^ n ∣ φ (f + g) - (φ f + φ g)) ∧
  (X : PowerSeries R) ^ n ∣ φ 1 - 1 ∧
  (∀ b, (X : PowerSeries R) ^ n ∣ φ (π b) - C (β b))

def IsJet (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (n : ℕ)
    (φ : A → PowerSeries R) : Prop :=
  IsRingHomMod π β n φ ∧
  (∀ f, (X : PowerSeries R) ^ n ∣ φ (m f) - rescale 2 (φ f)) ∧
  (∀ f, constantCoeff (φ f) = β (ε f)) ∧
  (∀ f, coeff 1 (φ f) = δ f)

theorem deriv_comp_m (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (E : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (hE : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f) (hEπ : ∀ a, E (π a) = 0) (f : A) :
    E (m f) = 2 * E f := by
  have hsq : ∀ x ∈ RingHom.ker ε ^ 2, E x = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [RingHom.mem_ker] at ha hb
      rw [hE, ha, hb]; simp
    · rw [map_add, ha, hb, add_zero]
  have hk : f - π (ε f) ∈ RingHom.ker ε := by
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply ε π, hεπ, RingHom.id_apply, sub_self]
  have h1 : m f = π (ε f) + (m (f - π (ε f)) - 2 * (f - π (ε f))) + (f - π (ε f)) + (f - π (ε f)) := by
    have : m (π (ε f)) = π (ε f) := by rw [← RingHom.comp_apply m π, hmπ]
    rw [map_sub, this]; ring
  have h2 : f = π (ε f) + (f - π (ε f)) := by ring
  rw [h1, map_add, map_add, map_add, hEπ, hsq _ (hm2 _ hk)]
  conv_rhs => rw [h2, map_add, hEπ]
  ring

end GlobalTheory.Nef.PathJet
