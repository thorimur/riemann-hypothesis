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
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_valuationSubring_ratFunc_residue_X_eq_zero :
    ∀ (k : Type) [Field k], ∃ (V : ValuationSubring (RatFunc k)) (c : k →+* V) (t : V), (algebraMap V (RatFunc k)).comp c = algebraMap k (RatFunc k) ∧ (t : RatFunc k) = RatFunc.X ∧ IsLocalRing.residue V t = 0 := by
  intro k _
  let v := (Polynomial.idealX k).valuation (RatFunc k)
  have hc : ∀ a : k, algebraMap k (RatFunc k) a ∈ v.valuationSubring := by
    intro a
    rw [Valuation.mem_valuationSubring_iff,
      IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
    exact (Polynomial.idealX k).valuation_le_one _
  have hX : v RatFunc.X < 1 := by
    rw [← RatFunc.algebraMap_X]
    exact ((Polynomial.idealX k).valuation_lt_one_iff_mem _).2 (by
      rw [Polynomial.idealX_span]; exact Ideal.mem_span_singleton_self _)
  have hX' : RatFunc.X ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]; exact hX.le
  refine ⟨v.valuationSubring, (algebraMap k (RatFunc k)).codRestrict v.valuationSubring hc,
    ⟨RatFunc.X, hX'⟩, ?_, rfl, ?_⟩
  · ext a; rfl
  · rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact ((Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one).1 hX

end GlobalTheory.FlagPush
