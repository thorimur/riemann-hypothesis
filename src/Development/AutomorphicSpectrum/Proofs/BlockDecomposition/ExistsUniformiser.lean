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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
open ValuativeRel
namespace GlobalTheory.CompanionTheory.LocalField
theorem exists_uniformiser (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ∃ ϖ : k, ∃ hϖ : ϖ ∈ (ValuativeRel.valuation k).integer, ϖ ≠ 0 ∧ ValuativeRel.valuation k (ϖ) < 1 ∧ (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) ∧ Irreducible (⟨ϖ, hϖ⟩ : (ValuativeRel.valuation k).integer) := by
  haveI : IsDiscreteValuationRing (ValuativeRel.valuation k).integer := inferInstance
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (ValuativeRel.valuation k).integer
  have hp0 : (p : k) ≠ 0 := by
    intro h
    exact hp.ne_zero (Subtype.ext h)
  have hle : ValuativeRel.valuation k (p : k) ≤ 1 := p.2
  have hnu : ¬ IsUnit p := hp.not_isUnit
  have hlt : ValuativeRel.valuation k (p : k) < 1 := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).2 h) hnu
  refine ⟨p, p.2, hp0, hlt, ?_, hp⟩
  intro x hx
  have hxi : x ∈ (ValuativeRel.valuation k).integer := le_of_lt hx
  set y : (ValuativeRel.valuation k).integer := ⟨x, hxi⟩ with hy
  have hynu : y ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation k).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).1 hu
    exact absurd this (ne_of_lt hx)
  rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton] at hynu
  obtain ⟨c, hc⟩ := hynu
  have hxc : x = (p : k) * (c : k) := by
    have := congrArg (Subtype.val) hc
    simpa using this
  rw [hxc, map_mul]
  have hc1 : ValuativeRel.valuation k (c : k) ≤ 1 := c.2
  exact mul_le_of_le_one_right' hc1
end GlobalTheory.CompanionTheory.LocalField
