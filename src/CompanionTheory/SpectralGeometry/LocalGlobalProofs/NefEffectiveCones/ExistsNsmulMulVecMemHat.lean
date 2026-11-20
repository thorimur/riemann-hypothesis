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

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.CompanionTheory.HatBound

theorem exists_nat_mul_integer (K : Type) [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 K, (r : K) = m * x := by
  have hx : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy, h⟩ := hx.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rcases Int.natAbs_eq y with h1 | h1
  · refine ⟨⟨y • x, h⟩, ?_⟩
    change y • x = _
    rw [zsmul_eq_mul]
    congr 1
    conv_lhs => rw [h1]
    simp only [Int.cast_natCast]
  · refine ⟨⟨-(y • x), h.neg⟩, ?_⟩
    change -(y • x) = _
    rw [zsmul_eq_mul, ← neg_mul]
    congr 1
    conv_lhs => rw [h1]
    simp only [Int.cast_neg, Int.cast_natCast, neg_neg]

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem exists_nsmul_mem_lattice [NumberField E] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨m', hm', hy⟩ := hy
    refine ⟨m * m', mul_pos hm hm', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx _
    · rw [mul_smul]; exact nsmul_mem hy _
  | smul c x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨m', hm', r, hr⟩ := exists_nat_mul_integer E c
    refine ⟨m * m', mul_pos hm hm', ?_⟩
    have : (m * m') • c • x = r • (m • x) := by
      funext i
      change (m * m') • (c * x i) = (r : E) * (m • x i)
      rw [hr, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [this]
    exact L.smul_mem r hx

end GlobalTheory.CompanionTheory.HatBound
