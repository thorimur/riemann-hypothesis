import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open Polynomial NumberField IsDedekindDomain IsLocalRing

section Generic

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (f : R →+* S)

theorem isPrimitiveRoot_map_of_natCast_ne_zero {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : S) ≠ 0) : IsPrimitiveRoot (f ζ) n := by
  have : NeZero (n : S) := ⟨hn⟩
  have : NeZero (n : R) := ⟨fun h => hn (by rw [← map_natCast f n, h, map_zero])⟩
  have hr : eval ζ (cyclotomic n R) = 0 := isRoot_cyclotomic_iff.mpr hζ
  apply isRoot_cyclotomic_iff.mp
  show eval (f ζ) (cyclotomic n S) = 0
  rw [← map_cyclotomic n f, eval_map, eval₂_hom, hr, map_zero]

theorem eq_of_map_eq_of_pow_eq_one {ζ : R} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (hn : (n : S) ≠ 0) {η η' : R} (hη : η ^ n = 1) (hη' : η' ^ n = 1) (h : f η = f η') :
    η = η' := by
  have hf := isPrimitiveRoot_map_of_natCast_ne_zero f hζ hn
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  obtain ⟨k, hk, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη'
  rw [map_pow, map_pow] at h
  rw [hf.pow_inj hj hk h]

theorem existsUnique_pow_eq_one_of_isPrimitiveRoot {ζ : R} {n : ℕ} [NeZero n]
    (hζ : IsPrimitiveRoot ζ n) (hn : (n : S) ≠ 0) {w : S} (hw : w ^ n = 1) :
    ∃! η : R, η ^ n = 1 ∧ f η = w := by
  have hf := isPrimitiveRoot_map_of_natCast_ne_zero f hζ hn
  obtain ⟨i, -, e⟩ := hf.eq_pow_of_pow_eq_one hw
  have hi : (ζ ^ i) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  refine ⟨ζ ^ i, ⟨hi, by rw [map_pow, e]⟩, ?_⟩
  rintro η ⟨hη, hfη⟩
  exact eq_of_map_eq_of_pow_eq_one f hζ hn hη hi (by rw [hfη, map_pow, e])

end Generic

theorem two_ne_zero_and_three_ne_zero_of_five_le_ringChar {k : Type*} [Field k]
    (h : 5 ≤ ringChar k) : (2 : k) ≠ 0 ∧ (3 : k) ≠ 0 := by
  refine ⟨fun h2 => ?_, fun h3 => ?_⟩
  · have := Nat.le_of_dvd (by norm_num) ((ringChar.spec k 2).mp (by exact_mod_cast h2))
    omega
  · have := Nat.le_of_dvd (by norm_num) ((ringChar.spec k 3).mp (by exact_mod_cast h3))
    omega

section NumberField

variable {L : Type*} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

end NumberField

end GroundTheory.Global
