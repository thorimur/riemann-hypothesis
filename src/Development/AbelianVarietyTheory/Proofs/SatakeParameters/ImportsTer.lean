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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.FiniteIndexSubgroup

open NumberField

private theorem exists_ne_zero_smul_mem_of_mem_span' {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    ∀ x ∈ Submodule.span E (L : Set (Fin n → E)), ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact L.add_mem (L.smul_mem b hax) (L.smul_mem a hbz)
  | smul c x _ hx =>
    obtain ⟨ν, hν, hνx⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : algebraMap (RingOfIntegers E) E b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hsc : algebraMap (RingOfIntegers E) E (b * ν) * c = algebraMap (RingOfIntegers E) E (a * ν) := by
      rw [← hab, map_mul, map_mul]
      field_simp
    refine ⟨b * ν, mul_ne_zero hb0 hν, ?_⟩
    have : (b * ν) • (c • x) = a • (ν • x) := by
      calc (b * ν) • (c • x) = (algebraMap (RingOfIntegers E) E (b * ν)) • (c • x) :=
            (algebraMap_smul E _ _).symm
        _ = (algebraMap (RingOfIntegers E) E (b * ν) * c) • x := smul_smul _ _ _
        _ = (algebraMap (RingOfIntegers E) E (a * ν)) • x := by rw [hsc]
        _ = (a * ν) • x := algebraMap_smul E _ _
        _ = a • (ν • x) := mul_smul _ _ _
    rw [this]
    exact L.smul_mem a hνx

theorem main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ ν : RingOfIntegers E, ν ≠ 0 ∧ ν • y ∈ L := exists_ne_zero_smul_mem_of_mem_span' L y (by rw [hL]; exact Submodule.mem_top)

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.span E (↑L : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E), ∃ (ν : NumberField.RingOfIntegers E), ν ≠ (0 : NumberField.RingOfIntegers E) ∧ ν • y ∈ L := by
  intro E _ _ n L hL y
  exact exists_ne_zero_smul_mem_of_mem_span' L y (by rw [hL]; exact Submodule.mem_top)

end GlobalTheory.FiniteIndexSubgroup
