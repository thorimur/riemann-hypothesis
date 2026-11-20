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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
open IsLocalRing

namespace GlobalTheory

theorem pi_eq_pow_ramificationIdx_mul_unit
    (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (P : Ideal (integralClosure S L)) [P.IsMaximal] :
    Irreducible π → algebraMap S (integralClosure S L) π ∈ P →
      ∃ ϖ : Localization.AtPrime P, Irreducible ϖ ∧ ∃ u : (Localization.AtPrime P)ˣ,
        algebraMap S (Localization.AtPrime P) π = ϖ ^ P.ramificationIdx S * (u : Localization.AtPrime P) := by
  intro hπ hπP
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hO0 : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    have h2 : algebraMap (integralClosure S L) L (algebraMap S (integralClosure S L) π) = 0 := by rw [h, map_zero]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S K L] at h2
    rw [map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective S K)] at h2
    exact hπ0 h2
  have hPbot : P ≠ ⊥ := fun h => hO0 (by rw [h] at hπP; simpa using hπP)
  haveI hA : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hPbot (Localization.AtPrime P)
  have hinj : Function.Injective (algebraMap (integralClosure S L) (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hx0 : algebraMap S (Localization.AtPrime P) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)]
    exact fun h => hO0 (hinj (by rw [h, map_zero]))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ

  have hunder : P.under S = Ideal.span {π} := by
    have hmem : π ∈ P.under S := by simpa [Ideal.under] using hπP
    have hne : P.under S ≠ ⊥ := fun h => hπ0 (by rw [h] at hmem; simpa using hmem)
    have hmax : (P.under S).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
    rw [IsLocalRing.eq_maximalIdeal hmax, hπ.maximalIdeal_eq]
  have hram : P.ramificationIdx S = n := by
    rw [Ideal.ramificationIdx_def, hunder, Ideal.map_span, Set.image_singleton, hn,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
      ENat.toNat_natCast]
  refine ⟨ϖ, hϖ, u, ?_⟩
  rw [hram, hn, mul_comm]

end GlobalTheory
