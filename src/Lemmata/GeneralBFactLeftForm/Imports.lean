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
import Mathlib.Topology.Sheaves.Presheaf

open Module Submodule
universe u v w

namespace Bl.general_b_fact_left_form

theorem goal1 {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (θ : ℝ) (j : Fin n) :
    θ ≤ f j ↔ (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ f i)).card := by
  constructor
  · intro h
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => θ ≤ f i) := by
      intro i hi
      rw [Finset.mem_Iic] at hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, le_trans h (hf hi)⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hn0
    have hn := not_le.mp hn0
    have hsub : Finset.univ.filter (fun i => θ ≤ f i) ⊆ Finset.Iio j := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_Iio]
      by_contra hji0
      have hji := not_lt.mp hji0
      exact absurd (lt_of_le_of_lt (hf hji) hn) (not_lt.mpr hi.2)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

end Bl.general_b_fact_left_form
