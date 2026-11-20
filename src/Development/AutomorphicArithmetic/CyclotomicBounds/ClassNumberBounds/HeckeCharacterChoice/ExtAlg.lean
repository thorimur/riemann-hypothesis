import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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

namespace KStar.Choice

def IsDiv (A : Type*) [CommGroup A] : Prop :=
  ∀ n : ℕ, n ≠ 0 → Function.Surjective fun a : A => a ^ n

theorem isDiv_complex_circle : IsDiv ℂˣ ∧ IsDiv Circle := by
  refine ⟨fun n hn z => ?_, fun n hn z => ?_⟩
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (Nat.pos_of_ne_zero hn)
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hw
      exact z.ne_zero hw.symm
    refine ⟨Units.mk0 w hw0, ?_⟩
    ext
    simp [hw]
  · refine ⟨Circle.exp ((z : ℂ).arg / n), ?_⟩
    simp only
    rw [← Circle.exp_natCast_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn), Circle.exp_arg]

theorem IsDiv.exists_extension {G A : Type*} [CommGroup G] [CommGroup A] (hA : IsDiv A)
    (H : Subgroup G) (f : H →* A) : ∃ F : G →* A, ∀ h : H, F h = f h := by
  have hsurj : ∀ {n : ℤ}, n ≠ 0 → Function.Surjective fun a : Additive A => n • a := by
    intro n hn x
    obtain ⟨y, hy⟩ := hA n.natAbs (Int.natAbs_ne_zero.mpr hn) (Additive.toMul x)
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul y, ?_⟩
      rw [h]
      change Additive.ofMul (y ^ ((n.natAbs : ℕ) : ℤ)) = x
      rw [zpow_natCast]
      simp only at hy
      rw [hy]
      rfl
    · refine ⟨Additive.ofMul y⁻¹, ?_⟩
      rw [h]
      change Additive.ofMul (y⁻¹ ^ (-((n.natAbs : ℕ) : ℤ))) = x
      rw [inv_zpow', neg_neg, zpow_natCast]
      simp only at hy
      rw [hy]
      rfl
  letI : DivisibleBy (Additive A) ℤ := divisibleByOfSMulRightSurj _ _ hsurj
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    (MonoidHom.toAdditive H.subtype) Subtype.val_injective (MonoidHom.toAdditive f)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  exact congrArg Additive.toMul (DFunLike.congr_fun hh (Additive.ofMul x))

end KStar.Choice
