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

namespace GlobalTheory.CompanionTheory.Ggeo

theorem adjoin_inv_isLocalization_away (Ω : Type) [Field Ω] [CharZero Ω] (A S' : Subalgebra ℚ Ω)
    (G : Set Ω) (hA : A = Algebra.adjoin ℚ G) (g : A) (hg : g ≠ 0)
    (hS : S' = Algebra.adjoin ℚ (insert (g : Ω)⁻¹ G)) (hle : A ≤ S') :
    @IsLocalization.Away A _ g S' _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  letI : Algebra A S' := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have hg0 : (g : Ω) ≠ 0 := fun h => hg (Subtype.ext h)
  have hinv : (g : Ω)⁻¹ ∈ S' := by
    rw [hS]; exact Algebra.subset_adjoin (Set.mem_insert _ _)
  have key : ∀ x ∈ S', ∃ (n : ℕ) (a : A), x * (g : Ω) ^ n = (a : Ω) := by
    intro x hx
    rw [hS] at hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.1 hx with rfl | hx
      · exact ⟨1, 1, by simp [hg0]⟩
      · refine ⟨0, ⟨x, ?_⟩, by simp⟩
        rw [hA]; exact Algebra.subset_adjoin hx
    | algebraMap r => exact ⟨0, algebraMap ℚ A r, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      refine ⟨n + m, a * g ^ m + b * g ^ n, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨n, a, ha⟩ := hx
      obtain ⟨m, b, hb⟩ := hy
      refine ⟨n + m, a * b, ?_⟩
      push_cast
      rw [← ha, ← hb]; ring
  refine IsLocalization.Away.mk g ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨(g : Ω)⁻¹, hinv⟩ : S') ?_
    apply Subtype.ext
    change (g : Ω) * (g : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ hg0
  · intro s
    obtain ⟨n, a, ha⟩ := key s s.2
    refine ⟨n, a, ?_⟩
    apply Subtype.ext
    change (s : Ω) * (g : Ω) ^ n = (a : Ω)
    exact ha
  · intro a b hab
    refine ⟨0, ?_⟩
    have : (a : Ω) = (b : Ω) := congrArg (fun x : S' => (x : Ω)) hab
    rw [Subtype.ext this]

end GlobalTheory.CompanionTheory.Ggeo
