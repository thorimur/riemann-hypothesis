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
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Ggeo

theorem exists_mem_count_normalizedFactors_span_eq :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I P : Ideal R), I ≠ ⊥ → P.IsPrime → P ≠ ⊥ →
      ∃ x ∈ I, x ≠ 0 ∧
        (normalizedFactors (Ideal.span {x})).count P = (normalizedFactors I).count P := by
  intro R _ _ I P hI hP hP0
  have hlt : I * P < I := by
    refine lt_of_le_of_ne Ideal.mul_le_left fun h => hP.ne_top ?_
    have h' : I * P = I * ⊤ := by rw [h, Ideal.mul_top]
    exact mul_left_cancel₀ hI h'
  obtain ⟨x, hxI, hxIP⟩ := SetLike.exists_of_lt hlt
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxIP (Submodule.zero_mem _)
  refine ⟨x, hxI, hx0, ?_⟩
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxI)
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hx0 hJ
  have hPJ : (normalizedFactors J).count P = 0 := by
    rw [Multiset.count_eq_zero]
    intro hmem
    obtain ⟨K, rfl⟩ := dvd_of_mem_normalizedFactors hmem
    apply hxIP
    have hle : Ideal.span {x} ≤ I * P := by
      rw [hJ, ← mul_assoc]
      exact Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self x)
  rw [hJ, normalizedFactors_mul hI hJ0, Multiset.count_add, hPJ, add_zero]

end GlobalTheory.CompanionTheory.Ggeo
