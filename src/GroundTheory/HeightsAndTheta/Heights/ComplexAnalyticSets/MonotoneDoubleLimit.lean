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
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology

theorem iterLim_eq_of_monotone {T : ℝ → ℝ → ℝ} {A B : ℝ → ℝ} {a b : ℝ}
    (hε : ∀ δ, 0 < δ → ∀ ε, 0 < ε → ∀ ε', ε ≤ ε' → T ε δ ≤ T ε' δ)
    (hδ : ∀ ε, 0 < ε → ∀ δ, 0 < δ → ∀ δ', δ ≤ δ' → T ε δ ≤ T ε δ')
    (hA : ∀ δ, 0 < δ → Tendsto (fun ε => T ε δ) (𝓝[>] 0) (𝓝 (A δ)))
    (hB : ∀ ε, 0 < ε → Tendsto (fun δ => T ε δ) (𝓝[>] 0) (𝓝 (B ε)))
    (ha : Tendsto A (𝓝[>] 0) (𝓝 a)) (hb : Tendsto B (𝓝[>] 0) (𝓝 b)) : a = b := by
  have below : ∀ x : ℝ, 0 < x → ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < y ∧ y ≤ x := fun x hx => by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds]
      with y hy hyx using ⟨hy, hyx.le⟩
  have keyA : ∀ ε, 0 < ε → ∀ δ, 0 < δ → A δ ≤ T ε δ := fun ε hε0 δ hδ0 =>
    le_of_tendsto (hA δ hδ0) (by
      filter_upwards [below ε hε0] with ε' h' using hε δ hδ0 ε' h'.1 ε h'.2)
  have keyB : ∀ ε, 0 < ε → ∀ δ, 0 < δ → B ε ≤ T ε δ := fun ε hε0 δ hδ0 =>
    le_of_tendsto (hB ε hε0) (by
      filter_upwards [below δ hδ0] with δ' h' using hδ ε hε0 δ' h'.1 δ h'.2)
  have h1 : ∀ ε, 0 < ε → a ≤ B ε := fun ε hε0 =>
    le_of_tendsto_of_tendsto ha (hB ε hε0) (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ using keyA ε hε0 δ hδ)
  have h2 : ∀ δ, 0 < δ → b ≤ A δ := fun δ hδ0 =>
    le_of_tendsto_of_tendsto hb (hA δ hδ0) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε using keyB ε hε δ hδ0)
  refine le_antisymm ?_ ?_
  · exact ge_of_tendsto hb (by filter_upwards [self_mem_nhdsWithin] with ε hε using h1 ε hε)
  · exact ge_of_tendsto ha (by filter_upwards [self_mem_nhdsWithin] with δ hδ using h2 δ hδ)

end GroundTheory.Heights₂.Heights
