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
open MeasureTheory Topology

namespace GlobalTheory

theorem measure_eq_zero_of_finite_inter_lines
    (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V) (hZ : MeasurableSet Z) (y : V)
    (h : ∀ x : V, {t : K | x + t • y ∈ Z}.Finite) : μ Z = 0 := by
  let ν : Measure K := Measure.addHaar
  have hc : Continuous (fun p : V × K => p.1 + p.2 • y) := by fun_prop
  have hS : MeasurableSet {p : V × K | p.1 + p.2 • y ∈ Z} := hc.measurable hZ
  have h1 : (μ.prod ν) {p : V × K | p.1 + p.2 • y ∈ Z} = 0 := by
    rw [Measure.measure_prod_null hS]
    refine Filter.Eventually.of_forall fun x => ?_
    exact (h x).measure_zero ν
  rw [Measure.prod_apply_symm hS] at h1
  have h2 : ∀ t : K, μ ((fun x => (x, t)) ⁻¹' {p : V × K | p.1 + p.2 • y ∈ Z}) = μ Z := by
    intro t
    exact measure_preimage_add_right μ (t • y) Z
  simp only [h2, lintegral_const, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact h1
  · exact absurd h1 (by
      rw [Measure.measure_univ_eq_zero]
      exact NeZero.ne ν)

end GlobalTheory
