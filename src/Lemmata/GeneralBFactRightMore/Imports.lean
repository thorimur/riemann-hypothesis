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

namespace Bl.general_b_fact_right_more

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] [StarRing.{0} E]
  (P : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} E)),
  Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
    And (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) a)
      (Exists.{1} fun (c : NumberField.RingOfIntegers.{0} E) ↦
        And (Not (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) c))
          (∀ (p : NumberField.RingOfIntegers.{0} E),
            Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) p →
              Exists.{1} fun (t : NumberField.RingOfIntegers.{0} E) ↦
                Eq.{1} (HMul.hMul.{0, 0, 0} c p) (HMul.hMul.{0, 0, 0} a t)))  := by
  intro E _ _ _ P
  have h0 : P.asIdeal ≠ ⊥ := P.ne_bot
  have h1 : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : P.asIdeal ^ 2 < P.asIdeal := Ideal.pow_lt_self _ h0 h1 2 le_rfl
  obtain ⟨a, haP, ha2⟩ := SetLike.exists_of_lt hlt
  have hdvd : P.asIdeal ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haP)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    apply ha2
    have h2 : Ideal.span {a} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp h2
  obtain ⟨c, hcJ, hcP⟩ := SetLike.not_le_iff_exists.mp hJP
  refine ⟨a, haP, c, hcP, fun p hp => ?_⟩
  have hm : c * p ∈ Ideal.span {a} := by
    rw [hJ, mul_comm c p]; exact Ideal.mul_mem_mul hp hcJ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨t, by rw [← ht, mul_comm]⟩

end Bl.general_b_fact_right_more
