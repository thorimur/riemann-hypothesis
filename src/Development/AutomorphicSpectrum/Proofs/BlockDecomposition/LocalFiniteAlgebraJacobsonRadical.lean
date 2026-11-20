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
import Mathlib.RingTheory.PicardGroup
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
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LocalFinite

theorem map_maximalIdeal_le_jacobson_and_pow_le :
    ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Module.Finite O R],
      Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ (⊥ : Ideal R).jacobson ∧
        ∃ N : ℕ, (⊥ : Ideal R).jacobson ^ N ≤
          Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) := by
  intro O R _ _ _ _ _
  haveI : Algebra.IsIntegral O R := Algebra.IsIntegral.of_finite O R
  set m := IsLocalRing.maximalIdeal O with hm
  set I : Ideal R := Ideal.map (algebraMap O R) m with hI
  refine ⟨?_, ?_⟩
  · refine le_sInf ?_
    rintro M ⟨-, hM⟩
    refine Ideal.map_le_iff_le_comap.mpr ?_
    haveI : (Ideal.comap (algebraMap O R) M).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  · have hle : m ≤ Ideal.comap (algebraMap O R) I := Ideal.le_comap_map
    let f : (O ⧸ m) →+* (R ⧸ I) := Ideal.quotientMap I (algebraMap O R) hle
    letI : Field (O ⧸ m) := Ideal.Quotient.field m
    letI : Algebra (O ⧸ m) (R ⧸ I) := f.toAlgebra
    have hcomp : (f.comp (Ideal.Quotient.mk m)).Finite := by
      have h1 : (algebraMap O R).Finite := RingHom.finite_algebraMap.mpr inferInstance
      have h2 : (Ideal.Quotient.mk I).Finite :=
        RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
      have h3 : f.comp (Ideal.Quotient.mk m) = (Ideal.Quotient.mk I).comp (algebraMap O R) := by
        ext x; simp [f]
      rw [h3]
      exact h2.comp h1
    have hf : f.Finite := RingHom.Finite.of_comp_finite hcomp
    haveI : Module.Finite (O ⧸ m) (R ⧸ I) := hf
    haveI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite (O ⧸ m) (R ⧸ I)
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
    refine ⟨N, ?_⟩
    have hmap : Ideal.map (Ideal.Quotient.mk I) (⊥ : Ideal R).jacobson ≤
        (⊥ : Ideal (R ⧸ I)).jacobson := by
      refine le_sInf ?_
      rintro P ⟨-, hP⟩
      refine Ideal.map_le_iff_le_comap.mpr ?_
      haveI : (Ideal.comap (Ideal.Quotient.mk I) P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      exact sInf_le ⟨bot_le, this⟩
    have hz : Ideal.map (Ideal.Quotient.mk I) ((⊥ : Ideal R).jacobson ^ N) = ⊥ := by
      rw [Ideal.map_pow]
      exact le_bot_iff.mp ((Ideal.pow_right_mono hmap N).trans hN.le)
    intro x hx
    have : Ideal.Quotient.mk I x = 0 := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hx
      rw [hz] at this
      simpa using this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory.CompanionTheory.LocalFinite
