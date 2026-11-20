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

namespace GlobalTheory.NatSmulIntegral

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ N : ℕ, 0 < N ∧ ∃ a : 𝓞 E, (a : E) = (N : E) * c := by
  have h : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz, hi⟩ := h.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz, ?_⟩
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq z with h1 | h1
  · refine ⟨⟨(z : E) * c, hi⟩, ?_⟩
    have : (z : E) = (z.natAbs : E) := by
      conv_lhs => rw [h1]
      exact Int.cast_natCast _
    rw [← this]; rfl
  · refine ⟨⟨-((z : E) * c), hi.neg⟩, ?_⟩
    have : (z : E) = -(z.natAbs : E) := by
      conv_lhs => rw [h1]
      rw [Int.cast_neg, Int.cast_natCast]
    have h2 : (z.natAbs : E) * c = -((z : E) * c) := by rw [this]; ring
    rw [h2]; rfl

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ N : ℕ, 0 < N ∧ N • y ∈ L := by
  have hy : y ∈ Submodule.span E (↑L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  have key : ∀ c : E, ∃ N : ℕ, 0 < N ∧ N • (c • y) ∈ L := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      intro c
      obtain ⟨N, hN, a, ha⟩ := exists_nat_mul_integral c
      refine ⟨N, hN, ?_⟩
      have h1 : N • (c • x) = a • x := by
        rw [← Nat.cast_smul_eq_nsmul E, smul_smul, ← ha]
        rfl
      rw [h1]
      exact L.smul_mem a hx
    | zero => intro c; exact ⟨1, one_pos, by simp⟩
    | add x y _ _ ihx ihy =>
      intro c
      obtain ⟨N, hN, h1⟩ := ihx c
      obtain ⟨M, hM, h2⟩ := ihy c
      refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
      rw [smul_add, smul_add]
      refine L.add_mem ?_ ?_
      · rw [mul_smul]; exact nsmul_mem h1 M
      · rw [mul_comm, mul_smul]; exact nsmul_mem h2 N
    | smul a x _ ih =>
      intro c
      rw [smul_smul]
      exact ih _
  simpa using key 1

end GlobalTheory.NatSmulIntegral
