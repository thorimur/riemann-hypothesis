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

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.redRoot :
    ∀ (R : Type) [CommRing R] [IsDomain R] (p : ℕ) [Fact p.Prime] (π : R →+* ZMod p) (M : ℕ) (ζ : R),
    p.Coprime M → IsPrimitiveRoot ζ M → IsPrimitiveRoot (π ζ) M ∧ M ∣ p - 1 := by
  intro R _ _ p hp π M ζ hcop hζ
  have hpp : p.Prime := hp.out
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with rfl | h
    · exact absurd (Nat.coprime_zero_right p |>.mp hcop) hpp.one_lt.ne'
    · exact h
  have hne : NeZero (M : ZMod p) := by
    refine ⟨fun h => ?_⟩
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  have hroot : (Polynomial.cyclotomic M R).IsRoot ζ := hζ.isRoot_cyclotomic hM
  have hroot' : (Polynomial.cyclotomic M (ZMod p)).IsRoot (π ζ) := by
    rw [← Polynomial.map_cyclotomic M π]
    exact hroot.map
  have hprim : IsPrimitiveRoot (π ζ) M := (Polynomial.isRoot_cyclotomic_iff).mp hroot'
  refine ⟨hprim, hprim.dvd_of_pow_eq_one _ ?_⟩
  exact ZMod.pow_card_sub_one_eq_one (hprim.ne_zero hM.ne')
