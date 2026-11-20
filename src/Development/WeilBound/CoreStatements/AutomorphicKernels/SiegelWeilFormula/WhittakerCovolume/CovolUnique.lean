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
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace PositivityTheory.SiegelWeilFormula.KWhit.MeasG

open MeasureTheory

theorem covol_unique {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [Countable Γ]
    {μ μ' : Measure G} [μ.IsAddHaarMeasure] [μ'.IsAddHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsAddFundamentalDomain Γ 𝓕 μ) (h' : IsAddFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) :
    μ' = μ := by
  have e : μ' = Measure.addHaarScalarFactor μ' μ • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  have h'' : IsAddFundamentalDomain Γ 𝓕' μ := h'.mono (Measure.absolutelyContinuous_isAddHaarMeasure μ μ')
  have hm : μ 𝓕' = μ 𝓕 := h''.measure_eq h
  have hc : (Measure.addHaarScalarFactor μ' μ : ENNReal) = 1 := by
    have := h1'
    rw [e, Measure.smul_apply, hm, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact this
  have hc' : Measure.addHaarScalarFactor μ' μ = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]

end PositivityTheory.SiegelWeilFormula.KWhit.MeasG
