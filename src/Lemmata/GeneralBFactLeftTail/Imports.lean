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
import Mathlib.Tactic.ENatToNat
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

open NumberField IsDedekindDomain Matrix

namespace Bl.general_b_fact_left_tail

variable {F : Type} [Field F] [NumberField F]

theorem goal1 (g : ℕ) (hg : g.Prime) : ∃ v : HeightOneSpectrum (𝓞 F), (g : 𝓞 F) ∈ v.asIdeal := by
  have hP : (Ideal.span {(g : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hg.ne_zero)).2 (Nat.prime_iff_prime_int.mp hg)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 F)
    (Ideal.span {(g : ℤ)}) ⊥ (by
      rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int]
      exact bot_le)
  have hgQ : (g : 𝓞 F) ∈ Q := by
    have h1 : (g : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 F)) := by
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  refine ⟨⟨Q, hQ, ?_⟩, hgQ⟩
  intro h
  rw [h] at hgQ
  have h0 : (g : 𝓞 F) = 0 := (Ideal.mem_bot).1 hgQ
  exact hg.ne_zero (by exact_mod_cast h0)

end Bl.general_b_fact_left_tail
