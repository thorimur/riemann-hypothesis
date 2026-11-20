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
import Mathlib.RingTheory.MvPowerSeries.Basic
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

namespace GlobalTheory.PowerSeriesShift

noncomputable def shift {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => MvPowerSeries.coeff (Finsupp.single i 1 + m) f

noncomputable def free {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O :=
  fun m : σ →₀ ℕ => if m i = 0 then MvPowerSeries.coeff m f else (0 : O)

theorem eq_X_mul_shift_add {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) :
    f = MvPowerSeries.X i * shift i f + free i f := by
  classical
  ext m
  rw [map_add, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  by_cases h : m i = 0
  · have h1 : ¬ Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_neg h1, zero_add]
    change _ = if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_pos h]
  · have h1 : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [if_pos h1, one_mul]
    change _ = MvPowerSeries.coeff (Finsupp.single i 1 + (m - Finsupp.single i 1)) f +
      if m i = 0 then MvPowerSeries.coeff m f else (0 : O)
    rw [if_neg h, add_zero, add_tsub_cancel_of_le h1]

theorem main : (let d1 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ (MvPowerSeries.coeff ((fun₀ | i => (1 : ℕ)) + m) : MvPowerSeries σ O → O) f); let d2 : {σ O : Type} → [CommRing O] → σ → MvPowerSeries σ O → MvPowerSeries σ O := @(fun {σ O : Type} [CommRing O] (i : σ) (f : MvPowerSeries σ O) (m : σ →₀ ℕ) ↦ if (m : σ → ℕ) i = (0 : ℕ) then (MvPowerSeries.coeff m : MvPowerSeries σ O → O) f else (0 : O)); ∀ {σ O : Type} [inst : CommRing O] (i : σ) (f : MvPowerSeries σ O), f = MvPowerSeries.X i * d1 i f + d2 i f) := by
  intro d1 d2 σ O _ i f
  exact eq_X_mul_shift_add i f

end GlobalTheory.PowerSeriesShift
