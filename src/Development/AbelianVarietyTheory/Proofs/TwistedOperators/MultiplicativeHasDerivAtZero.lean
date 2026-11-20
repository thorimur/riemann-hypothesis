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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem multiplicative_hasDerivAt_zero : ∀ (lam : ℝ → ℂ), lam 0 = 1 →
    (∀ s t, lam (s + t) = lam s * lam t) → ContinuousAt lam 0 → ∃ c : ℂ, HasDerivAt lam c 0 := by
  intro lam h0 hmul hc
  have hcont : Continuous lam := by
    rw [continuous_iff_continuousAt]
    intro t
    have h1 : ContinuousAt (fun x => lam (x - t)) t := by
      apply ContinuousAt.comp (g := lam) (f := fun x => x - t)
      · simpa using hc
      · exact (continuous_id.sub continuous_const).continuousAt
    have h2 : (fun x => lam t * lam (x - t)) = lam := by
      funext x; rw [← hmul]; congr 1; ring
    rw [← h2]; exact continuousAt_const.mul h1
  set F : ℝ → ℂ := fun u => ∫ x in (0:ℝ)..u, lam x with hF
  have hFd : ∀ b, HasDerivAt F (lam b) b := fun b =>
    (hcont.integral_hasStrictDerivAt 0 b).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, F δ ≠ 0 := by
    have := (hFd 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    exact this.exists
  have hi : ∀ a b : ℝ, IntervalIntegrable lam MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have key : ∀ t, lam t * F δ = F (t + δ) - F t := by
    intro t
    calc lam t * F δ = ∫ s in (0:ℝ)..δ, lam (t + s) := by
          simp only [hF, hmul]; rw [intervalIntegral.integral_const_mul]
      _ = ∫ s in (t + 0)..(t + δ), lam s := intervalIntegral.integral_comp_add_left lam t
      _ = F (t + δ) - F t := by
          simp only [add_zero, hF]
          exact (intervalIntegral.integral_interval_sub_left (hi 0 (t + δ)) (hi 0 t)).symm
  have hd : HasDerivAt (fun t => (F (t + δ) - F t) * (F δ)⁻¹)
      ((lam (0 + δ) - lam 0) * (F δ)⁻¹) 0 := by
    have h1 : HasDerivAt (fun t => F (t + δ)) (lam (0 + δ)) 0 :=
      HasDerivAt.comp_add_const 0 δ (hFd (0 + δ))
    exact (h1.sub (hFd 0)).mul_const _
  refine ⟨_, hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)⟩
  simp only
  rw [← key t, mul_assoc, mul_inv_cancel₀ hδ, mul_one]

end GlobalTheory
