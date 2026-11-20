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
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory.SpanSingleInlMembership

theorem mem_span_single_inl_iff {g : ℕ} (S : Finset (Fin g)) (u : Fin g ⊕ Fin g → ℤ) :
    u ∈ Submodule.span ℤ ((fun (k : Fin g) ↦ Pi.single (Sum.inl k) (1 : ℤ)) '' (↑S : Set (Fin g))) ↔
      (∀ (k : Fin g), u (Sum.inr k) = (0 : ℤ)) ∧ ∀ k ∉ S, u (Sum.inl k) = (0 : ℤ) := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨fun k => by simp, fun k hk => ?_⟩
      have hne : k ≠ j := fun e => hk (e ▸ hj)
      simp [hne]
    | zero => simp
    | add x y _ _ hx hy =>
      exact ⟨fun k => by simp [hx.1 k, hy.1 k], fun k hk => by simp [hx.2 k hk, hy.2 k hk]⟩
    | smul a x _ hx =>
      exact ⟨fun k => by simp [hx.1 k], fun k hk => by simp [hx.2 k hk]⟩
  · rintro ⟨h1, h2⟩
    have hu : u = ∑ k ∈ S, u (Sum.inl k) • (Pi.single (Sum.inl k) (1 : ℤ) : Fin g ⊕ Fin g → ℤ) := by
      funext i
      rcases i with j | j
      · by_cases hj : j ∈ S
        · simp [Finset.sum_apply, Pi.single_apply, hj]
        · simp [Finset.sum_apply, Pi.single_apply, hj, h2 j hj]
      · simp [Finset.sum_apply, h1 j]
    rw [hu]
    exact Submodule.sum_mem _ fun k hk =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.SpanSingleInlMembership
