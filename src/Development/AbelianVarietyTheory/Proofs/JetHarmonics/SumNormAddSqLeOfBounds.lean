import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Monotonicity.Lemmas
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

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_norm_add_sq_le_of_bounds :
    ∀ (V ι : Type) [NormedAddCommGroup V] [Fintype ι] (u v : ι → V) (c s N : ℝ), 0 ≤ c → 0 ≤ s → 0 ≤ N → ∑ i, ‖u i‖ ^ 2 ≤ c ^ 2 * N → ∑ i, ‖v i‖ ^ 2 ≤ s ^ 2 * N → ∑ i, ‖u i + v i‖ ^ 2 ≤ (c + s) ^ 2 * N := by
  intro V ι _ _ u v c s N hc hs hN hu hv
  have hcs : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hv0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : (∑ i, ‖u i‖ * ‖v i‖) ^ 2 ≤ (c * s * N) ^ 2 := by
    calc _ ≤ _ := hcs
      _ ≤ (c ^ 2 * N) * (s ^ 2 * N) := mul_le_mul hu hv hv0 (by positivity)
      _ = _ := by ring
  have h2 : ∑ i, ‖u i‖ * ‖v i‖ ≤ c * s * N :=
    (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun i _ => by positivity) (by positivity)
      two_ne_zero).1 h1
  have h3 : ∑ i, ‖u i + v i‖ ^ 2 ≤ ∑ i, (‖u i‖ ^ 2 + 2 * (‖u i‖ * ‖v i‖) + ‖v i‖ ^ 2) := by
    refine Finset.sum_le_sum fun i _ => ?_
    calc ‖u i + v i‖ ^ 2 ≤ (‖u i‖ + ‖v i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
      _ = _ := by ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h3
  nlinarith

end GlobalTheory
