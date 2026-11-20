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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory.DivisibleUnits

theorem units_zpow_surjective {F : Type} [Field F] [IsAlgClosed F] {n : ℤ} (hn : n ≠ 0) :
    Function.Surjective (fun a : Fˣ => a ^ n) := by
  have nat_root : ∀ (m : ℕ), 0 < m → ∀ x : Fˣ, ∃ y : Fˣ, y ^ m = x := by
    intro m hm x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : F) hm
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact x.ne_zero hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    ext
    simp [hz]
  intro x
  rcases Int.lt_or_gt_of_ne hn with h | h
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x⁻¹
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = -(n.natAbs : ℤ) := by omega
    rw [this, zpow_neg, zpow_natCast, hy, inv_inv]
  · obtain ⟨y, hy⟩ := nat_root n.natAbs (Int.natAbs_pos.mpr hn) x
    refine ⟨y, ?_⟩
    show y ^ n = x
    have : n = (n.natAbs : ℤ) := by omega
    rw [this, zpow_natCast, hy]

noncomputable def divisibleUnits (F : Type) [Field F] [IsAlgClosed F] :
    DivisibleBy (Additive Fˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Fˣ) ℤ (fun {n} hn x => by
    obtain ⟨y, hy⟩ := units_zpow_surjective (F := F) hn (Additive.toMul x)
    exact ⟨Additive.ofMul y, by simpa using congrArg Additive.ofMul hy⟩)

theorem exists_extension {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) :
    ∃ κ : M →* Fˣ, ∀ x : H, κ (Φ x) = χ x := by
  letI := divisibleUnits F
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive Fˣ)).extension_property_addMonoidHom
    (MonoidHom.toAdditive Φ) hΦ (MonoidHom.toAdditive χ)
  refine ⟨MonoidHom.toAdditive.symm h, fun x => ?_⟩
  have := DFunLike.congr_fun hh (Additive.ofMul x)
  exact this

theorem target : ∀ {H M F : Type} [inst : CommGroup H] [inst_1 : CommGroup M] [inst_2 : Field F] [IsAlgClosed F] (Φ : H →* M), Function.Injective (⇑Φ : H → M) → ∀ (χ : H →* Fˣ), ∃ (κ : M →* Fˣ), ∀ (x : H), (κ : M → Fˣ) ((Φ : H → M) x) = (χ : H → Fˣ) x :=
  fun Φ hΦ χ => exists_extension Φ hΦ χ

end GlobalTheory.DivisibleUnits
