import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.DedekindDomain.Different
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem map_mem_differentIdeal (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E)
    (hd : d ∈ differentIdeal ℤ (𝓞 E)) : s d ∈ differentIdeal ℤ (𝓞 E) := by
  have key : IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) =
      1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := coeSubmodule_differentIdeal ℤ ℚ (𝓞 E)
  let τ : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E) s
  have hτ : ∀ b : 𝓞 E, τ (algebraMap (𝓞 E) E b) = algebraMap (𝓞 E) E (s b) :=
    fun b => IsFractionRing.ringEquivOfRingEquiv_algebraMap s b
  let τq : E ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := τ) fun x => τ.toRingHom.map_rat_algebraMap x
  have htr : ∀ x : E, Algebra.trace ℚ E (τ x) = Algebra.trace ℚ E x :=
    fun x => Algebra.trace_eq_of_algEquiv τq x
  have h1 : ∀ a : E, a ∈ (1 : Submodule (𝓞 E) E) → τ a ∈ (1 : Submodule (𝓞 E) E) := by
    intro a ha
    obtain ⟨b, rfl⟩ := Submodule.mem_one.1 ha
    exact Submodule.mem_one.2 ⟨s b, (hτ b).symm⟩
  have hdual : ∀ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E),
      τ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    intro y hy
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    have h2 := hy (τ a) (h1 a ha)
    rw [Algebra.traceForm_apply] at h2 ⊢
    rw [← htr, map_mul, RingEquiv.apply_symm_apply]
    exact h2
  have hd' : algebraMap (𝓞 E) E d ∈
      (1 / Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) : Submodule (𝓞 E) E) := by
    rw [← key]
    exact (IsLocalization.mem_coeSubmodule _ _).2 ⟨d, hd, rfl⟩
  have hs : algebraMap (𝓞 E) E (s d) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) := by
    rw [key, Submodule.mem_div_iff_forall_mul_mem]
    intro y hy
    have h2 := (Submodule.mem_div_iff_forall_mul_mem.1 hd') (τ.symm y) (hdual y hy)
    have h3 := h1 _ h2
    rwa [map_mul, hτ, RingEquiv.apply_symm_apply] at h3
  obtain ⟨y, hy, hyd⟩ := (IsLocalization.mem_coeSubmodule _ _).1 hs
  rwa [IsFractionRing.injective (𝓞 E) E hyd] at hy

theorem map_mem_differentIdeal_iff : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E), s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) := by
  intro E _ _ s d
  constructor
  · intro h
    have := map_mem_differentIdeal E s.symm (s d) h
    rwa [RingEquiv.symm_apply_apply] at this
  · exact map_mem_differentIdeal E s d

end PositivityTheory.UnitarySelfGeneration
