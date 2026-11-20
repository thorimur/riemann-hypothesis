import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

open scoped PowerSeries.WithPiTopology in
theorem UpperTheory.V.Pa.BC.ps_ev :
    ∀ (R K : Type) [CommRing R] [CommRing K] (x : R →+* PowerSeries K), ∃ f : PowerSeries R →+* PowerSeries K, (∀ a, f (PowerSeries.C a) = x a) ∧ f PowerSeries.X = PowerSeries.X := by
  intro R K _ _ x
  letI : UniformSpace R := ⊥
  letI : UniformSpace K := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  haveI : DiscreteUniformity K := ⟨rfl⟩
  refine ⟨PowerSeries.eval₂Hom (φ := x) (a := PowerSeries.X) continuous_of_discreteTopology
    PowerSeries.HasEval.X, ?_, ?_⟩
  · intro a
    rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]
