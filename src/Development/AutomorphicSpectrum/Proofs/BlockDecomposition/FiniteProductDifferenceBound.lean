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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.Mass.MeanV

theorem abs_prod_sub_prod_le_sum_powerset (V : Type) (a : V → ℝ) (A U : Finset V) (hAU : A ⊆ U) :
    |∏ v ∈ U, a v - ∏ v ∈ A, a v| ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by
  have hexp : ∀ S : Finset V, ∏ v ∈ S, a v = ∑ D ∈ S.powerset, ∏ v ∈ D, (a v - 1) := by
    intro S
    rw [← Finset.prod_one_add]
    exact Finset.prod_congr rfl fun v _ => by ring
  have hfilt : U.powerset.filter (fun D => D ⊆ A) = A.powerset := by
    ext D
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.trans hAU, h⟩⟩
  rw [hexp U, hexp A, ← Finset.sum_filter_add_sum_filter_not U.powerset (fun D => D ⊆ A), hfilt,
    add_sub_cancel_left]
  calc |∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, (a v - 1)|
      ≤ ∑ D ∈ U.powerset with ¬ D ⊆ A, |∏ v ∈ D, (a v - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ D ∈ U.powerset with ¬ D ⊆ A, ∏ v ∈ D, |a v - 1| := by simp_rw [Finset.abs_prod]

end GlobalTheory.CompanionTheory.Mass.MeanV
