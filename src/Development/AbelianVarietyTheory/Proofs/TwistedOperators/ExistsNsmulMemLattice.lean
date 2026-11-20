import Mathlib.Algebra.Module.Lattice
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

namespace GlobalTheory.NatMultipleInLattice

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have h1 := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have e : ((y.natAbs : ℕ) : E) * a = y • a := by
      rw [zsmul_eq_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1
  · have e : ((y.natAbs : ℕ) : E) * a = -(y • a) := by
      rw [zsmul_eq_mul, ← neg_mul]
      congr 1
      conv_rhs => rw [h]
      simp
    rw [e]
    exact h1.neg

theorem exists_nsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (x : Fin n → E) : ∃ D : ℕ, D ≠ 0 ∧ D • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨F, hF, hz⟩ := hz
    refine ⟨D * F, mul_ne_zero hD hF, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy F
    · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hz D
  | smul a y _ hy =>
    obtain ⟨D, hD, hy⟩ := hy
    obtain ⟨m, hm, hi⟩ := exists_nat_mul_integral a
    refine ⟨m * D, mul_ne_zero hm hD, ?_⟩
    have key := L.smul_mem (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) hy
    have : (m * D) • a • y =
        (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y := by
      have h3 : (⟨(m : E) * a, hi⟩ : NumberField.RingOfIntegers E) • D • y
          = ((m : E) * a) • D • y := rfl
      rw [h3]
      ext i
      simp only [Pi.smul_apply]
      simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
      ring
    rw [this]; exact key

end GlobalTheory.NatMultipleInLattice
