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

open MeasureTheory

namespace GlobalTheory

theorem continuous_of_map_add_mul_of_continuousAt_zero (ν : ℝ → ℂ)
    (hm : ∀ s t, ν (s + t) = ν s * ν t) (hc : ContinuousAt ν 0) : Continuous ν := by
  rw [continuous_iff_continuousAt]
  intro x
  have h1 : ν = fun y => ν x * ν (y - x) := by
    funext y
    rw [← hm]
    congr 1
    ring
  rw [h1]
  refine continuousAt_const.mul ?_
  have h2 : ContinuousAt (fun y : ℝ => y - x) x := by fun_prop
  exact ContinuousAt.comp (f := fun y : ℝ => y - x) (by simpa using hc) h2

theorem exists_hasDerivAt_zero_of_map_add_mul :
    ∀ ν : ℝ → ℂ, ν 0 = 1 → (∀ s t, ν (s + t) = ν s * ν t) → ContinuousAt ν 0 →
      ∃ a : ℂ, HasDerivAt ν a 0 := by
  intro ν h0 hm hc0
  have hc := continuous_of_map_add_mul_of_continuousAt_zero ν hm hc0
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, ν x with hF
  have hd : ∀ u, HasDerivAt F (ν u) u := fun u => (hc.deriv_integral ν 0 u ▸
    (hc.integral_hasStrictDerivAt 0 u).hasDerivAt.differentiableAt.hasDerivAt)
  have hex : ∃ δ, F δ ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hz : F = fun _ => 0 := funext hne
    have h1 := hd 0
    rw [hz, h0] at h1
    exact one_ne_zero (h1.unique (hasDerivAt_const (0:ℝ) (0:ℂ)))
  obtain ⟨δ, hδ⟩ := hex
  have key : ∀ t, ν t = (F (t + δ) - F t) / F δ := by
    intro t
    rw [eq_div_iff hδ]
    have e1 : F (t + δ) - F t = ∫ x in t..(t + δ), ν x := by
      simp only [hF]
      exact intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)
    have e2 : ∫ x in t..(t + δ), ν x = ∫ x in (0:ℝ)..δ, ν (t + x) := by
      rw [intervalIntegral.integral_comp_add_left ν t, add_zero]
    rw [e1, e2]
    simp only [hm, hF]
    rw [intervalIntegral.integral_const_mul]
  have h1 : HasDerivAt (fun t => F (t + δ)) (ν (0 + δ)) 0 := (hd (0 + δ)).comp_add_const 0 δ
  refine ⟨(ν (0 + δ) - ν 0) / F δ, ?_⟩
  have h2 := (h1.sub (hd 0)).div_const (F δ)
  have h3 : ν = fun t => (F (t + δ) - F t) / F δ := funext key
  conv => arg 1; rw [h3]
  exact h2

end GlobalTheory
