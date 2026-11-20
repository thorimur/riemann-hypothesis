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
import Mathlib.Tactic.ENatToNat
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

open Matrix

namespace GlobalTheory

def transvectionUnit {R : Type} [CommRing R] {r : ℕ} {i j : Fin r} (h : i ≠ j) : GL (Fin r) R :=
  ⟨transvection i j (1 : R), transvection i j (-1 : R),
    by rw [transvection_mul_transvection_same _ _ h]; simp,
    by rw [transvection_mul_transvection_same _ _ h]; simp⟩

theorem transvectionUnit_pow_val {R : Type} [CommRing R] {r : ℕ} {i j : Fin r} (h : i ≠ j)
    (n : ℕ) :
    ((transvectionUnit (R := R) h ^ n : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)
      = transvection i j (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih]
    change transvection i j (n : R) * transvection i j (1 : R) = _
    rw [transvection_mul_transvection_same _ _ h]
    simp

theorem orderOf_transvectionUnit {R : Type} [CommRing R] (q : ℕ) [CharP R q] {r : ℕ}
    {i j : Fin r} (h : i ≠ j) : orderOf (transvectionUnit (R := R) h) = q := by
  have key : ∀ n : ℕ, orderOf (transvectionUnit (R := R) h) ∣ n ↔ q ∣ n := by
    intro n
    rw [orderOf_dvd_iff_pow_eq_one, ← CharP.cast_eq_zero_iff R q n, Units.ext_iff,
      transvectionUnit_pow_val, Units.val_one]
    constructor
    · intro hn
      have := congrFun (congrFun hn i) j
      simpa [transvection, one_apply_ne h] using this
    · intro hn
      rw [hn, transvection_zero]
  exact Nat.dvd_antisymm ((key q).2 dvd_rfl) ((key _).1 dvd_rfl)

theorem two_mul_pow_four_dvd_card_generalLinearGroup :
    ∀ (R : Type) [CommRing R] [Finite R] (p : ℕ), Odd p → CharP R (p ^ 4) → 1 < p →
      ∀ r : ℕ, 2 ≤ r → 2 * p ^ 4 ∣ Nat.card (GL (Fin r) R) := by
  intro R _ _ p hp hchar h1 r hr
  have hij : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp
  have hq : p ^ 4 ∣ Nat.card (GL (Fin r) R) := by
    rw [← orderOf_transvectionUnit (R := R) (p ^ 4) hij]
    exact orderOf_dvd_natCard _
  have h2 : (2 : R) ≠ 0 := by
    intro h
    have hd : p ^ 4 ∣ 2 := (CharP.cast_eq_zero_iff R (p ^ 4) 2).1 (by exact_mod_cast h)
    have hle := Nat.le_of_dvd (by norm_num) hd
    have : 2 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h1 4
    omega
  have hneg : orderOf (-1 : GL (Fin r) R) = 2 := by
    apply orderOf_eq_prime
    · simp
    · intro h
      have h' := congrArg (fun u : GL (Fin r) R =>
        (u : Matrix (Fin r) (Fin r) R) ⟨0, by omega⟩ ⟨0, by omega⟩) h
      simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h'
      apply h2
      linear_combination -h'
  have h2d : 2 ∣ Nat.card (GL (Fin r) R) := by
    rw [← hneg]
    exact orderOf_dvd_natCard _
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd
    (Nat.Coprime.pow_right 4 ((Nat.coprime_two_left).2 hp)) h2d hq

end GlobalTheory
