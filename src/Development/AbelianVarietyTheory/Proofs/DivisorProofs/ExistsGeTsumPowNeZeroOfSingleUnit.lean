import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.Topology.Sheaves.Init
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory

theorem tsum_pow_eventually_ne_zero : ∀ {ι : Type} (a : ι → ℂ) (i0 : ι) (k0 : ℕ), a i0 = 1 → (∀ i, ‖a i‖ ≤ 1) → (∀ i, i ≠ i0 → ‖a i‖ < 1) → Summable (fun i => ‖a i‖ ^ k0) → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ ∑' i, a i ^ k ≠ 0 := by
  intro ι a i0 k0 h0 h1 hlt hs N
  classical
  have hlim : Filter.Tendsto (fun k : ℕ => ∑' i, a i ^ k) Filter.atTop
      (nhds (∑' i, (if i = i0 then (1:ℂ) else 0))) := by
    apply tendsto_tsum_of_dominated_convergence (bound := fun i => ‖a i‖ ^ k0) hs
    · intro i
      by_cases hi : i = i0
      · subst hi; simp [h0]
      · simp only [hi, if_false]
        exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hlt i hi)
    · filter_upwards [Filter.eventually_ge_atTop k0] with k hk i
      rw [norm_pow]
      exact pow_le_pow_of_le_one (norm_nonneg _) (h1 i) hk
  rw [tsum_ite_eq] at hlim
  have hev := hlim.eventually_ne one_ne_zero
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
  exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩

end GlobalTheory
