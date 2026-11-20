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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_pow_valuation_div_sub_one_le :
    ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E), c ≠ 0 →
      ∀ n : ℕ, ∃ N : ℕ, ∀ k : 𝓞 E, k - c ∈ v.asIdeal ^ N →
        v.valuation E ((k : E) / (c : E) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  intro E _ _ v c hc n
  set e : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {c})).factors with he
  have hval : v.valuation E (c : E) = WithZero.exp (-(e : ℤ)) := by
    have h := HeightOneSpectrum.valuation_of_algebraMap (K := E) v c
    have h' : v.valuation E (c : E) = v.intValuation c := h
    rw [h', v.intValuation_if_neg hc]
  have hcE : (c : E) ≠ 0 := by
    simpa using hc
  refine ⟨n + e, fun k hk => ?_⟩
  have hle : v.intValuation (k - c) ≤ WithZero.exp (-((n + e : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem (k - c) (n + e)).2 hk
  have hdiff : v.valuation E (((k - c : 𝓞 E)) : E) = v.intValuation (k - c) :=
    HeightOneSpectrum.valuation_of_algebraMap (K := E) v (k - c)
  have heq : (k : E) / (c : E) - 1 = (((k - c : 𝓞 E)) : E) / (c : E) := by
    push_cast
    field_simp
  rw [heq, map_div₀, hval, hdiff]
  have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-(e : ℤ)) := WithZero.exp_pos
  rw [div_le_iff₀ hpos, ← WithZero.exp_add]
  have hexp : -(n : ℤ) + -(e : ℤ) = -((n + e : ℕ) : ℤ) := by
    push_cast
    ring
  rwa [hexp]

end GlobalTheory
