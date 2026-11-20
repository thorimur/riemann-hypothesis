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
import Mathlib.Topology.Sheaves.Presheaf

open Finset DirichletCharacter
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.PrimesAP

def fibre {N M : ℕ} [NeZero M] (h : N ∣ M) (a : (ZMod N)ˣ) : Finset (ZMod M)ˣ :=
  Finset.univ.filter (fun u => ZMod.unitsMap h u = a)

theorem intervalIntegrable_inv_log {Y X : ℝ} (hY : 2 ≤ Y) (hX : 2 ≤ X) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume Y X := by
  apply ContinuousOn.intervalIntegrable
  have : ∀ t ∈ Set.uIcc Y X, 2 ≤ t := fun t ht => le_trans (le_min hY hX) ht.1
  refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    have := this t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [this]
  · intro t ht
    exact (Real.log_pos (by linarith [this t ht])).ne'

theorem le_integral_inv_log {Y X : ℝ} (hY : 2 ≤ Y) (hX : Y ≤ X) :
    (X - Y) / Real.log X ≤ ∫ t in Y..X, 1 / Real.log t := by
  have : (X - Y) / Real.log X = ∫ _ in Y..X, 1 / Real.log X := by
    simp [div_eq_mul_inv]
  rw [this]
  apply intervalIntegral.integral_mono_on hX (by simp) (intervalIntegrable_inv_log hY (hY.trans hX))
  intro t ht
  exact one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1])) (Real.log_le_log (by linarith [ht.1]) ht.2)

end GlobalTheory.CompanionTheory.PrimesAP
