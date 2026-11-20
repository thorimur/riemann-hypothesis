import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic
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

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cptNull :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (l : Filter ι) (K : H →L[ℂ] H) (x : ι → H) (C : ℝ), IsCompactOperator K → (∀ i, ‖x i‖ ≤ C) →
      (∀ y, Tendsto (fun i => ⟪y, x i⟫_ℂ) l (𝓝 0)) → Tendsto (fun i => K (x i)) l (𝓝 0) := by
  intro H _ _ _ ι l K x C hK hb hw
  obtain ⟨S, hS, hsub⟩ := hK.image_closedBall_subset_compact C
  refine hS.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall fun i => hsub ⟨x i, by simpa using hb i, rfl⟩) ?_
  intro y _ hy
  have h1 : Tendsto (fun i => ⟪y, K (x i)⟫_ℂ) l (𝓝 0) := by
    simpa [ContinuousLinearMap.adjoint_inner_left] using hw (ContinuousLinearMap.adjoint K y)
  have h2 : MapClusterPt ⟪y, y⟫_ℂ l (fun i => ⟪y, K (x i)⟫_ℂ) :=
    hy.continuousAt_comp (f := fun z => ⟪y, z⟫_ℂ) (by fun_prop)
  have h3 : ⟪y, y⟫_ℂ = 0 := eq_of_nhds_neBot (h2.clusterPt.mono h1).neBot
  exact inner_self_eq_zero.1 h3
