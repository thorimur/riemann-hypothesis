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

open Real

namespace GlobalTheory

open Filter Asymptotics in

theorem log_add_rpow_mul_log_pow_le_rpow :
    ∀ a b c C κ : ℝ, ∀ p : ℕ, 0 ≤ a → a < b → 0 < κ → ∃ x0 : ℝ, ∀ x ≥ x0,
      c * Real.log x + C * x ^ a * Real.log x ^ p + C ≤ κ * x ^ b := by
  intro a b c C κ p ha hab hκ
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have h1 : (fun x : ℝ => c * Real.log x) =o[atTop] fun x => x ^ b :=
    (isLittleO_log_rpow_atTop hb).const_mul_left c
  have h2 : (fun x : ℝ => C * x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
    have hl : (fun x : ℝ => Real.log x ^ p) =o[atTop] fun x => x ^ (b - a) := by
      have := isLittleO_log_rpow_rpow_atTop (p : ℝ) (sub_pos.2 hab)
      simpa [Real.rpow_natCast] using this
    have hm : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop]
        fun x => x ^ a * x ^ (b - a) :=
      (isBigO_refl (fun x : ℝ => x ^ a) atTop).mul_isLittleO hl
    have hm' : (fun x : ℝ => x ^ a * Real.log x ^ p) =o[atTop] fun x => x ^ b := by
      refine hm.congr' (Eventually.of_forall fun _ => rfl) ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simpa [mul_assoc] using hm'.const_mul_left C
  have h3 : (fun _ : ℝ => C) =o[atTop] fun x => x ^ b := by
    rw [isLittleO_const_left]
    right
    exact tendsto_norm_atTop_atTop.comp (tendsto_rpow_atTop hb)
  have h := (h1.add h2).add h3
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 ((h.bound hκ).and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨hbd, hxpos⟩ := hx0 x hx
  have hpos : 0 < x ^ b := Real.rpow_pos_of_pos hxpos b
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos] at hbd
  exact (le_abs_self _).trans hbd

end GlobalTheory
