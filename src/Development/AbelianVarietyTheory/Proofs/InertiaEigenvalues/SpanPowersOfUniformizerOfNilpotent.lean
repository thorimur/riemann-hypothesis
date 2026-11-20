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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open Polynomial

namespace GlobalTheory

theorem span_powers_of_uniformizer_of_nilpotent :
    ∀ (C B : Type) [CommRing C] [CommRing B] (φ : C →+* B) (π : B) (L : C) (e m : ℕ),
      (∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π}) → π ^ e ∈ Ideal.span {φ L} → φ L ^ m = 0 →
      ∀ x : B, ∃ c : Fin e → C, x = ∑ j, φ (c j) * π ^ (j : ℕ) := by
  intro C B _ _ φ π L e m hsurj he hm
  have step1 : ∀ k : ℕ, ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range k, φ (c j) * π ^ j + π ^ k * w := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, x, by simp⟩
    | succ k ih =>
      intro x
      obtain ⟨c, w, hx⟩ := ih x
      obtain ⟨y, hy⟩ := hsurj w
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hy
      refine ⟨fun j => if j = k then y else c j, z, ?_⟩
      rw [Finset.sum_range_succ]
      beta_reduce
      rw [if_pos rfl]
      have hsum : ∑ j ∈ Finset.range k, φ (if j = k then y else c j) * π ^ j
          = ∑ j ∈ Finset.range k, φ (c j) * π ^ j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_neg (Finset.mem_range.mp hj).ne]
      rw [hsum, hx]
      have hw : w = φ y + z * π := by rw [hz]; ring
      rw [hw]; ring
  have step1' : ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L * w := by
    intro x
    obtain ⟨c, w, hx⟩ := step1 e x
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp he
    exact ⟨c, u * w, by rw [hx, ← hu]; ring⟩
  have step2 : ∀ n : ℕ, ∀ x : B, ∃ c : ℕ → C, ∃ w : B,
      x = ∑ j ∈ Finset.range e, φ (c j) * π ^ j + φ L ^ n * w := by
    intro n
    induction n with
    | zero => intro x; exact ⟨0, x, by simp⟩
    | succ n ih =>
      intro x
      obtain ⟨c, w, hx⟩ := ih x
      obtain ⟨d, w', hw⟩ := step1' w
      refine ⟨fun j => c j + L ^ n * d j, w', ?_⟩
      have key : ∑ j ∈ Finset.range e, φ (c j + L ^ n * d j) * π ^ j
          = ∑ j ∈ Finset.range e, φ (c j) * π ^ j
            + φ L ^ n * ∑ j ∈ Finset.range e, φ (d j) * π ^ j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_add, map_mul, map_pow]
        ring
      rw [key, hx, hw]
      ring
  intro x
  obtain ⟨c, w, hx⟩ := step2 m x
  refine ⟨fun j => c j, ?_⟩
  rw [hx, hm, zero_mul, add_zero]
  exact (Fin.sum_univ_eq_sum_range (fun j => φ (c j) * π ^ j) e).symm

end GlobalTheory
