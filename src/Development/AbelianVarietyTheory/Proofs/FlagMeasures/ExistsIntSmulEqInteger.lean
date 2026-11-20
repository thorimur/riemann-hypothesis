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

namespace GlobalTheory.IntSmulIntegerEq

theorem exists_int_smul_eq_integer {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers E,
      algebraMap (NumberField.RingOfIntegers E) E a = M • c := by
  have hQ : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have hZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hQ
  obtain ⟨M, hM, hint⟩ := hZ.exists_integral_multiple
  exact ⟨M, hM, ⟨M • c, hint⟩, rfl⟩

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N₁, h₁, hx⟩ := hx
    obtain ⟨N₂, h₂, hy⟩ := hy
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : (N₁ * N₂) • (x + y) = N₂ • (N₁ • x) + N₁ • (N₂ • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm N₂ N₁]
    rw [e]
    exact L.add_mem (zsmul_mem hx N₂) (zsmul_mem hy N₁)
  | smul c x _ hx =>
    obtain ⟨N, hN, hx⟩ := hx
    obtain ⟨M, hM, a, ha⟩ := exists_int_smul_eq_integer c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have e : (M * N) • (c • x) = a • (N • x) := by
      rw [← algebraMap_smul E a, ha, smul_assoc, mul_smul, smul_comm N c x]
    rw [e]
    exact L.smul_mem a hx

end GlobalTheory.IntSmulIntegerEq
