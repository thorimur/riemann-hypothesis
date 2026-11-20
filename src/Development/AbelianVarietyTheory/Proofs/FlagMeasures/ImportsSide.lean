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

namespace GlobalTheory.SaturatedSublattice

open NumberField

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤ → ∀ (v : Fin n → E), ∃ (D : NumberField.RingOfIntegers E), D ≠ (0 : NumberField.RingOfIntegers E) ∧ D • v ∈ Λ := by
  intro E _ _ n Λ hspan v
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hspan]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨D1, hD1, h1⟩ := hx
    obtain ⟨D2, hD2, h2⟩ := hy
    refine ⟨D1 * D2, mul_ne_zero hD1 hD2, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem D2 h1
    · rw [mul_smul]; exact Λ.smul_mem D1 h2
  | smul a x _ hx =>
    obtain ⟨D, hD, h⟩ := hx
    obtain ⟨⟨b, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    simp only at hd
    refine ⟨(d : RingOfIntegers E) * D, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) hD, ?_⟩
    have key : ((d : RingOfIntegers E) * D) • (a • x) = b • (D • x) := by
      rw [← algebraMap_smul E ((d : RingOfIntegers E) * D) (a • x), ← algebraMap_smul E b (D • x),
        ← algebraMap_smul E D x, smul_smul, smul_smul, map_mul, ← hd]
      congr 1
      ring
    rw [key]
    exact Λ.smul_mem b h

end GlobalTheory.SaturatedSublattice
