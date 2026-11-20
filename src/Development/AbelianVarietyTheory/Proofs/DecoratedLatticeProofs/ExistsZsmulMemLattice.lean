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

namespace GlobalTheory.LatticeIntegerMultiple

open NumberField

theorem exists_int_mul_mem {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (m : ℤ) (b : RingOfIntegers E), m ≠ 0 ∧ algebraMap (RingOfIntegers E) E b = m • a := by
  have hQ : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have hZ : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 hQ
  obtain ⟨m, hm, hi⟩ := hZ.exists_integral_multiple
  exact ⟨m, ⟨m • a, hi⟩, hm, rfl⟩

theorem exists_zsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) [Submodule.IsLattice E L] (x : Fin n → E) :
    ∃ (m : ℤ), m ≠ (0 : ℤ) ∧ m • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [Submodule.IsLattice.span_eq_top (A := E)]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨k, hk, hz⟩ := hz
    refine ⟨m * k, mul_ne_zero hm hk, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hy k
    · rw [mul_smul]; exact zsmul_mem hz m
  | smul a y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨k, b, hk, hb⟩ := exists_int_mul_mem a
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have h : (k * m) • a • y = b • (m • y) := by
      rw [← algebraMap_smul E b, hb, mul_smul, smul_comm m a y, smul_assoc]
    rw [h]
    exact L.smul_mem b hy

end GlobalTheory.LatticeIntegerMultiple
