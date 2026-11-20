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
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem mvPowerSeries_lift_quotient :
    ∀ (O σ : Type) [CommRing O] (I : Ideal O), (∀ g : MvPowerSeries σ (O ⧸ I), ∃ f : MvPowerSeries σ O, map (Ideal.Quotient.mk I) f = g ∧ (constantCoeff g = 0 → constantCoeff f = 0)) ∧ (∀ f : MvPowerSeries σ O, map (Ideal.Quotient.mk I) f = 0 ↔ ∀ α, coeff α f ∈ I) ∧ ∀ (a : O) (f : MvPowerSeries σ O), (∀ α, a ∣ coeff α f) ↔ ∃ g, f = a • g := by
  classical
  intro O σ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro g
    let s : O ⧸ I → O := fun x => if x = 0 then 0 else Quotient.out x
    have hs : ∀ x, Ideal.Quotient.mk I (s x) = x := by
      intro x
      by_cases hx : x = 0
      · simp [s, hx]
      · simp only [s, if_neg hx]
        exact Ideal.Quotient.mk_out x
    let f : MvPowerSeries σ O := fun α => s (coeff α g)
    refine ⟨f, ?_, ?_⟩
    · ext α
      rw [coeff_map]
      exact hs _
    · intro h0
      have : coeff (0 : σ →₀ ℕ) g = 0 := by simpa [coeff_zero_eq_constantCoeff_apply] using h0
      rw [← coeff_zero_eq_constantCoeff_apply]
      show s (coeff 0 g) = 0
      simp [s, this]
  · intro f
    constructor
    · intro h α
      have := congrArg (coeff α) h
      rw [coeff_map, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro h
      ext α
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h α)
  · intro a f
    constructor
    · intro h
      choose c hc using h
      let g : MvPowerSeries σ O := fun α => c α
      have hg : ∀ α, coeff α g = c α := fun _ => rfl
      refine ⟨g, ?_⟩
      ext α
      rw [coeff_smul, hg, hc α]
    · rintro ⟨g, rfl⟩ α
      rw [coeff_smul]
      exact dvd_mul_right _ _

end GlobalTheory
