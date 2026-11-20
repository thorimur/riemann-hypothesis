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
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Exp
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

noncomputable section

namespace Formalism.HermitianLattices.WeilRepresentation.PadicSquareSumIntegrality

open Finset

def allEmbeddingsUnitCircle : Subgroup ℂˣ where
  carrier := {w | ∀ s : ℂ →+* ℂ, ‖s (w : ℂ)‖ = 1}
  one_mem' := by intro s; simp
  mul_mem' := by
    intro a b ha hb s
    simp only [Units.val_mul, map_mul, norm_mul, ha s, hb s, mul_one]
  inv_mem' := by
    intro a ha s
    simp only [Units.val_inv_eq_inv_val, map_inv₀, norm_inv, ha s, inv_one]

theorem exists_pow_eq_unit_circle (w : allEmbeddingsUnitCircle) (n : ℕ) (hn : n ≠ 0) : ∃ b : allEmbeddingsUnitCircle, b ^ n = w := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq ((w : ℂˣ) : ℂ) (Nat.pos_of_ne_zero hn)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hβ
    exact (Units.ne_zero (w : ℂˣ)) hβ.symm
  refine ⟨⟨Units.mk0 β hβ0, ?_⟩, ?_⟩
  · intro s
    have h1 : ‖s ((w : ℂˣ) : ℂ)‖ = 1 := w.2 s
    rw [← hβ, map_pow, norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp h1
  · apply Subtype.ext; apply Units.ext
    simp [hβ]

instance unitCircleDivisibleNat : DivisibleBy (Additive allEmbeddingsUnitCircle) ℕ where
  div a n := if h : n = 0 then 0 else Additive.ofMul (Classical.choose (exists_pow_eq_unit_circle a.toMul n h))
  div_zero a := by simp
  div_cancel {n} a hn := by
    simp only [hn, dite_false]
    have := Classical.choose_spec (exists_pow_eq_unit_circle a.toMul n hn)
    change Additive.ofMul ((Classical.choose (exists_pow_eq_unit_circle a.toMul n hn)) ^ n) = a
    rw [this]; rfl

instance unitCircleDivisibleInt : DivisibleBy (Additive allEmbeddingsUnitCircle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _

section Dwork

open MvPowerSeries

variable {K : Type} [Field K] {ι : Type}

def integralPowerSeriesSubring (W : Subring K) (ι : Type) : Subring (MvPowerSeries ι K) where
  carrier := {u | ∀ m, coeff m u ∈ W}
  mul_mem' := by
    intro a b ha hb m
    classical
    rw [coeff_mul]
    exact W.sum_mem fun x _ => W.mul_mem (ha _) (hb _)
  one_mem' := by
    intro m
    classical
    rw [coeff_one]
    split_ifs
    exacts [W.one_mem, W.zero_mem]
  add_mem' := by intro a b ha hb m; rw [map_add]; exact W.add_mem (ha m) (hb m)
  zero_mem' := by intro m; rw [map_zero]; exact W.zero_mem
  neg_mem' := by intro a ha m; rw [map_neg]; exact W.neg_mem (ha m)

def PDivisibleSeries (W : Subring K) (p : ℕ) (u : MvPowerSeries ι K) : Prop :=
  ∀ m, ∃ w ∈ W, coeff m u = (p : K) * w

end Dwork

section Cor

open MvPowerSeries

variable {K : Type} [Field K] [CharZero K] {ι : Type}

abbrev multivariateExpSeries (H : MvPowerSeries ι K) : MvPowerSeries ι K :=
  PowerSeries.subst H (PowerSeries.exp K)

def truncatedExpSeries (N : ℕ) (H : MvPowerSeries ι K) : MvPowerSeries ι K :=
  ∑ d ∈ range (N + 1), C (PowerSeries.coeff d (PowerSeries.exp K)) * H ^ d

end Cor

end Formalism.HermitianLattices.WeilRepresentation.PadicSquareSumIntegrality
