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

namespace DedekindLocalUniformizer
end DedekindLocalUniformizer

theorem UpperTheory.Reformulated.B.Yde5.main :
    ∀ {R : Type} [inst : CommRing R] [IsDedekindDomain R] (P : Ideal R),
      P.IsMaximal → P ≠ ⊥ → ∃ (π : R), π ≠ (0 : R) ∧ π ∈ P ∧ ∃ s ∉ P, ∀ y ∈ P, ∃ (c : R), s * y = π * c := by
  intro R _ _ P hmax hbot
  haveI : P.IsPrime := hmax.isPrime
  have hlt : P ^ (1 + 1) < P ^ 1 := Ideal.pow_succ_lt_pow hbot 1
  rw [pow_one] at hlt
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hπ2 (Ideal.zero_mem _)
  refine ⟨π, hπ0, hπP, ?_⟩
  have hle : Ideal.span {π} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 hπP
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 hle
  have hJP : ¬ J ≤ P := by
    intro h
    apply hπ2
    have : Ideal.span {π} ≤ P ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  refine ⟨s, hsP, fun y hy => ?_⟩
  have hmem : s * y ∈ Ideal.span {π} := by
    rw [hJ, mul_comm s y]; exact Ideal.mul_mem_mul hy hsJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨c, by rw [← hc, mul_comm]⟩
