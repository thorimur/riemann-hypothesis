import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem logDeriv_local {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) (hne : ¬ ∀ᶠ s in 𝓝 ρ, f s = 0) :
    ∃ m : ℕ, (m = 0 ↔ f ρ ≠ 0) ∧ (m : ℕ∞) = analyticOrderAt f ρ ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv f s / f s = (m : ℂ) / (s - ρ) + h s := by
  have htop : analyticOrderAt f ρ ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp htop
  set m := analyticOrderNatAt f ρ with hm
  refine ⟨m, ?_, Nat.cast_analyticOrderNatAt htop, fun s => deriv g s / g s,
    hg.deriv.div hg hg0, ?_⟩
  · rw [← hf.analyticOrderAt_eq_zero, ← Nat.cast_analyticOrderNatAt htop]
    exact Nat.cast_eq_zero.symm
  · have hev : ∀ᶠ s in 𝓝 ρ, (∀ᶠ z in 𝓝 s, f z = (z - ρ) ^ m • g z) ∧ g s ≠ 0 ∧ AnalyticAt ℂ g s :=
      (Filter.Eventually.eventually_nhds hfg).and
        ((hg.continuousAt.eventually_ne hg0).and hg.eventually_analyticAt)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hsne
    obtain ⟨hs1, hs2, hs3⟩ := hs
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hsne
    have hd : HasDerivAt (fun z => (z - ρ) ^ m * g z)
        (↑m * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s) s :=
      (((hasDerivAt_id' s).sub_const ρ).pow m).mul hs3.differentiableAt.hasDerivAt
    have e1 : deriv f s = deriv (fun z => (z - ρ) ^ m * g z) s := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hs1] with z hz
      rw [hz, smul_eq_mul]
    have e2 : f s = (s - ρ) ^ m * g s := by simpa only [smul_eq_mul] using hs1.self_of_nhds
    rw [e1, hd.deriv, e2]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]
      simp
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]
      field_simp

end Deduction

end
