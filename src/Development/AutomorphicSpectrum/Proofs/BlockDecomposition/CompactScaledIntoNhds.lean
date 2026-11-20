import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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

open ValuativeRel MeasureTheory Matrix
open Filter Topology

namespace GlobalTheory.CompanionTheory.CompactScaling

theorem exists_pow_smul_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (K : Set (Fin n → k)), IsCompact K → ∀ U ∈ nhds (0 : Fin n → k), ∀ ϖ : k, valuation k ϖ < 1 → ∃ l : ℕ, ∀ x ∈ K, ϖ ^ l • x ∈ U := by
  intro k _ _ _ _ n K hK U hU ϖ hϖ
  have hpow : Tendsto (fun l : ℕ => ϖ ^ l) atTop (𝓝 (0 : k)) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hϖ γ
    rw [eventually_atTop]
    refine ⟨m, fun l hl => ?_⟩
    simp only [Set.mem_ofPred_eq, map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hl) hm
  have hnear : ∀ᶠ c in 𝓝 (0 : k), ∀ x ∈ K, c • x ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun x _ => ?_)
    have hcont : Continuous (fun p : k × (Fin n → k) => p.1 • p.2) :=
      continuous_fst.smul continuous_snd
    have hlim : Tendsto (fun p : k × (Fin n → k) => p.1 • p.2) (𝓝 (0, x)) (𝓝 0) := by
      simpa using hcont.tendsto (0, x)
    exact hlim hU
  exact (hpow.eventually hnear).exists

end GlobalTheory.CompanionTheory.CompactScaling
