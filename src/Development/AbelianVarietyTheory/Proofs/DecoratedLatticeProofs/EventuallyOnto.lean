import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

open scoped Topology
open Filter

namespace GlobalTheory.ApproxOnto

theorem eventually_onto : ∀ (X : Type) (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] (T : ℕ → W →ₗ[ℂ] W), (∀ (ψ : W) (x : X), Tendsto (fun i => (T i ψ).1 x) atTop (𝓝 (ψ.1 x))) → ∃ i, Function.Surjective (T i) := by
  intro X W _ T hT
  have hconv : ∀ ψ : W, Tendsto (fun i => T i ψ) atTop (𝓝 ψ) := by
    intro ψ
    rw [tendsto_subtype_rng]
    exact tendsto_pi_nhds.2 (fun x => hT ψ x)
  let b := Module.finBasis ℂ W
  have hmat : Tendsto (fun i => LinearMap.toMatrix b b (T i)) atTop
      (𝓝 (LinearMap.toMatrix b b LinearMap.id)) := by
    refine tendsto_pi_nhds.2 fun k => tendsto_pi_nhds.2 fun j => ?_
    simp only [LinearMap.toMatrix_apply]
    have hc : Continuous (fun w : W => b.repr w k) := (b.coord k).continuous_of_finiteDimensional
    exact (hc.tendsto _).comp (hconv (b j))
  have hdet : Tendsto (fun i => LinearMap.det (T i)) atTop (𝓝 1) := by
    have := ((continuous_id.matrix_det).tendsto _).comp hmat
    simpa [LinearMap.det_toMatrix, Function.comp_def] using this
  obtain ⟨i, hi⟩ := (hdet.eventually_ne one_ne_zero).exists
  refine ⟨i, ?_⟩
  have hu : IsUnit (T i) := (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hi)
  exact ((Module.End.isUnit_iff _).1 hu).2

end GlobalTheory.ApproxOnto
