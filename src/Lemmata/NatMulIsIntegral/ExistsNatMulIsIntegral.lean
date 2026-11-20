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

namespace Bl.NatMulIsIntegral

private theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = y.natAbs := ⟨_, rfl⟩
  rcases Int.natAbs_eq y with h | h <;> rw [← hm] at h <;> subst h
  · refine ⟨m, by omega, ?_⟩
    simpa [zsmul_eq_mul] using hint
  · refine ⟨m, by omega, ?_⟩
    have h2 := hint.neg
    simpa [zsmul_eq_mul] using h2

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {n : Nat}
  {L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)} {z : Fin n → E},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) z →
    Exists.{1} fun (N : Nat) ↦ And (LT.lt.{0} 0 N) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} N z)) := by
  intro E _ _ n L z hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have key : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [key]
    exact L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, hdi⟩ := exists_nat_mul_isIntegral c
    refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
    have key : (⟨(d : E) * c, hdi⟩ : NumberField.RingOfIntegers E) • (a • x) = (d * a) • (c • x) := by
      rw [algebra_compatible_smul E (⟨(d : E) * c, hdi⟩ : NumberField.RingOfIntegers E)]
      show ((d : E) * c) • (a • x) = _
      rw [mul_smul, smul_comm c a x, Nat.cast_smul_eq_nsmul E, smul_smul]
    rw [← key]
    exact L.smul_mem _ hax

end Bl.NatMulIsIntegral
