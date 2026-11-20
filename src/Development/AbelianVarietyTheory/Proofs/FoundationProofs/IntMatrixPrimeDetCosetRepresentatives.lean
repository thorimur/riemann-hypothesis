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

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem exists_right_div_upperTriangular_prime_det (q : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (k : ℕ)
    (h1 : (q : ℤ) ∣ m 0 1 - m 0 0 * k) (h2 : (q : ℤ) ∣ m 1 1 - m 1 0 * k) :
    ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨c, hc⟩ := h2
  refine ⟨!![m 0 0, a; m 1 0, c], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination -ha | linear_combination ha | linear_combination -hc

theorem cosetPrimeDet : ∀ (q : ℕ), q.Prime → ∀ m : Matrix (Fin 2) (Fin 2) ℤ, m.det = q →
    (∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![(q : ℤ), 0; 0, 1] = m) ∨
    ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
  intro q hq m hdet
  have := Fact.mk hq
  have : NeZero q := ⟨hq.ne_zero⟩
  rw [Matrix.det_fin_two] at hdet
  have hd : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ℤ) - ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
    have : ((m 0 0 * m 1 1 - m 0 1 * m 1 0 : ℤ) : ZMod q) = 0 := by
      rw [hdet]; simp
    push_cast at this
    exact this

  have dv : ∀ x : ℤ, (x : ZMod q) = 0 → (q : ℤ) ∣ x := fun x hx =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp hx

  have fin : ∀ t : ZMod q, ((m 0 1 : ℤ) : ZMod q) - (m 0 0 : ℤ) * t = 0 →
      ((m 1 1 : ℤ) : ZMod q) - (m 1 0 : ℤ) * t = 0 →
      ∃ k : ℕ, k < q ∧ ∃ g : Matrix (Fin 2) (Fin 2) ℤ, g * !![1, (k : ℤ); 0, (q : ℤ)] = m := by
    intro t ht1 ht2
    refine ⟨t.val, ZMod.val_lt t, exists_right_div_upperTriangular_prime_det q m t.val (dv _ ?_) (dv _ ?_)⟩
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht1
    · push_cast; rw [ZMod.natCast_zmod_val]; exact ht2
  by_cases ha : ((m 0 0 : ℤ) : ZMod q) = 0
  · by_cases hc : ((m 1 0 : ℤ) : ZMod q) = 0
    ·
      left
      obtain ⟨x, hx⟩ := dv _ ha
      obtain ⟨y, hy⟩ := dv _ hc
      refine ⟨!![x, m 0 1; y, m 1 1], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | linear_combination -hx | linear_combination hx | linear_combination -hy
    · right
      have h01 : ((m 0 1 : ℤ) : ZMod q) = 0 := by
        have : ((m 0 1 : ℤ) : ZMod q) * (m 1 0 : ℤ) = 0 := by
          linear_combination -hd + ((m 1 1 : ℤ) : ZMod q) * ha
        exact (mul_eq_zero.mp this).resolve_right hc
      have hinv := mul_inv_cancel₀ hc
      refine fin (((m 1 1 : ℤ) : ZMod q) * ((m 1 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
      · rw [ha, h01]; ring
      · linear_combination -((m 1 1 : ℤ) : ZMod q) * hinv
  · right
    have hinv := mul_inv_cancel₀ ha
    refine fin (((m 0 1 : ℤ) : ZMod q) * ((m 0 0 : ℤ) : ZMod q)⁻¹) ?_ ?_
    · linear_combination -((m 0 1 : ℤ) : ZMod q) * hinv
    · linear_combination ((m 0 0 : ℤ) : ZMod q)⁻¹ * hd - ((m 1 1 : ℤ) : ZMod q) * hinv

end GlobalTheory
