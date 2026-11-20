import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Convex
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
import Std.Tactic.BVDecide.Normalize.Prop

open Set

namespace GlobalTheory

theorem punctured_unit_disc_eq_exp_image :
    Metric.ball (0:ℂ) 1 \ {0} = Complex.exp '' {z : ℂ | z.re < 0} := by
  ext w
  constructor
  · rintro ⟨hb, h0⟩
    have h0' : w ≠ 0 := h0
    refine ⟨Complex.log w, ?_, Complex.exp_log h0'⟩
    rw [Set.mem_setOf_eq, Complex.log_re]
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact Real.log_neg (norm_pos_iff.mpr h0') hb
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hz
    · exact Complex.exp_ne_zero z

theorem isPreconnected_punctured_unit_disc :
    IsPreconnected (Metric.ball (0:ℂ) 1 \ {0}) := by
  rw [punctured_unit_disc_eq_exp_image]
  exact (convex_halfSpace_re_lt 0).isPreconnected.image _ Complex.continuous_exp.continuousOn

theorem isPreconnected_polydisc_first_coords_ne_zero :
    ∀ (n a : ℕ) (ha : a ≤ n), _root_.IsPreconnected {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0} := by
  intro n a ha
  have hS : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin a, z (Fin.castLE ha i) ≠ 0}
      = Set.pi univ (fun k : Fin n => if (k:ℕ) < a then Metric.ball (0:ℂ) 1 \ {0} else Metric.ball (0:ℂ) 1) := by
    ext z
    rw [ball_pi _ one_pos]
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Pi.zero_apply]
    constructor
    · rintro ⟨hb, hne⟩ k
      split_ifs with hk
      · exact ⟨hb k, fun h => hne ⟨k, hk⟩ (by simpa using h)⟩
      · exact hb k
    · intro h
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have := h k
        split_ifs at this
        · exact this.1
        · exact this
      · have := h (Fin.castLE ha i)
        rw [if_pos (by simp)] at this
        exact this.2
  rw [hS]
  apply isPreconnected_univ_pi
  intro k
  split_ifs
  · exact isPreconnected_punctured_unit_disc
  · exact (convex_ball (0:ℂ) 1).isPreconnected

end GlobalTheory
