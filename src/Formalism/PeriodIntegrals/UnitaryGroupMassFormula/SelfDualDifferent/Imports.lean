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
import Mathlib.Topology.Sheaves.Init

noncomputable section
open NumberField

namespace PI.UnitaryGroupMassFormula.KerSelfDual

theorem int_map {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E) (x : 𝓞 E) :
    ∃ x' : 𝓞 E, algebraMap (𝓞 E) E x' = cj (algebraMap (𝓞 E) E x) := by
  have h : IsIntegral ℤ (algebraMap (𝓞 E) E x) := (IsIntegralClosure.isIntegral ℤ E x).algebraMap
  have h' : IsIntegral ℤ (cj (algebraMap (𝓞 E) E x)) :=
    IsIntegral.map ((cj : E →+* E).toIntAlgHom) h
  exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp h'

theorem one_map {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E) {z : E}
    (hz : z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) :
    cj z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
  rw [FractionalIdeal.mem_one_iff] at hz ⊢
  obtain ⟨x, rfl⟩ := hz
  exact int_map cj x

theorem inv_map {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E) (hinv : ∀ x, cj (cj x) = x)
    (𝔟 𝔟c : Ideal (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ 𝔟c ↔ ∃ y ∈ 𝔟, cj (y : E) = (x : E))
    (hb : 𝔟 ≠ ⊥) (hbc : 𝔟c ≠ ⊥) (y : E) :
    y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ ↔
      cj y ∈ ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
  have hb0 : ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb
  have hbc0 : ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hbc
  rw [FractionalIdeal.mem_inv_iff hb0, FractionalIdeal.mem_inv_iff hbc0]
  constructor
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    obtain ⟨b, hb𝔟, hbw⟩ := (hc w').mp hw'
    have h1 := h (algebraMap (𝓞 E) E b) (FractionalIdeal.mem_coeIdeal_of_mem _ hb𝔟)
    have h2 := one_map cj h1
    rw [map_mul] at h2
    have e : (algebraMap (𝓞 E) E w') = cj (algebraMap (𝓞 E) E b) := hbw.symm
    rw [e]
    exact h2
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb𝔟, rfl⟩ := hw
    obtain ⟨c, hcE⟩ := int_map cj b
    have hc𝔟 : c ∈ 𝔟c := (hc c).mpr ⟨b, hb𝔟, hcE.symm⟩
    have h1 := h (algebraMap (𝓞 E) E c) (FractionalIdeal.mem_coeIdeal_of_mem _ hc𝔟)
    rw [hcE, ← map_mul] at h1
    have h2 := one_map cj h1
    rw [hinv] at h2
    exact h2

end PI.UnitaryGroupMassFormula.KerSelfDual
