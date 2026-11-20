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

namespace GlobalTheory.NatMulIntegral

open NumberField

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]
    exact hi
  · have h' : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h', Int.cast_neg, neg_mul]
    exact hi.neg

theorem nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (d : ℕ) {x : Fin n → E} (hx : x ∈ L) :
    (d : E) • x ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx d

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hez⟩ := hz
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have h1 := nat_smul_mem L e hdx
    have h2 := nat_smul_mem L d hez
    have : ((d * e : ℕ) : E) • (x + z) = (e : E) • (d : E) • x + (d : E) • (e : E) • z := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (e : E)]
    rw [this]
    exact L.add_mem h1 h2
  | smul a x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hea⟩ := exists_nat_mul_isIntegral a
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    let b : RingOfIntegers E := ⟨(e : E) * a, hea⟩
    have h1 : b • (d : E) • x ∈ L := L.smul_mem b hdx
    have : ((d * e : ℕ) : E) • a • x = b • (d : E) • x := by
      rw [← algebraMap_smul E b]
      change _ = ((e : E) * a) • (d : E) • x
      rw [smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact h1

end GlobalTheory.NatMulIntegral
