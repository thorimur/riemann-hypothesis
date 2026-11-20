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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory

theorem haar_map_mul_right_eq_of_fundamentalDomain (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H)) (κ : Measure N) (𝓝 : Set N)
    (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤) (n₀ : N) :
    κ.map (· * n₀) = κ := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨((x : N) : H), x.2⟩ : Γ)) ?_
    intro a b h
    have h' : ((a : N) : H) = ((b : N) : H) := congrArg (fun y : Γ => (y : H)) h
    exact Subtype.ext (Subtype.ext h')
  haveI : (κ.map (· * n₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right κ n₀
  have hc := Measure.isMulLeftInvariant_eq_smul (κ.map (· * n₀)) κ
  set c := Measure.haarScalarFactor (κ.map (· * n₀)) κ
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf N) ((· * n₀) ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv (quasiMeasurePreserving_mul_right κ n₀) (e := id) bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : κ ((· * n₀) ⁻¹' 𝓝) = κ 𝓝 := h𝓝'.measure_eq h𝓝
  have h0 : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hmap : (κ.map (· * n₀)) 𝓝 = κ ((· * n₀) ⁻¹' 𝓝) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight n₀) 𝓝
  have h1 : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    calc (c : ENNReal) * κ 𝓝 = (c • κ) 𝓝 := by simp [Measure.smul_apply]
      _ = (κ.map (· * n₀)) 𝓝 := by rw [hc]
      _ = 1 * κ 𝓝 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end GlobalTheory
