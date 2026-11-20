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

namespace GlobalTheory

theorem freeModule_adicComplete_separated : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → (∀ a : R, (∀ n : ℕ, ∃ b : R, a = ϖ ^ n * b) → a = 0) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M], (∀ x : ℕ → M, ∃ y : M, ∀ n : ℕ, ∃ z : M, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) ∧ (∀ m : M, (∀ n : ℕ, ∃ z : M, m = ϖ ^ n • z) → m = 0) := by
  intro R _ ϖ hc hs M _ _ _ _
  classical
  let b := Module.Free.chooseBasis R M
  haveI : Fintype (Module.Free.ChooseBasisIndex R M) := Module.Free.ChooseBasisIndex.fintype R M
  constructor
  · intro x
    choose a ha using fun i => hc (fun j => b.equivFun (x j) i)
    refine ⟨b.equivFun.symm a, fun n => ?_⟩
    choose c hc' using fun i => ha i n
    refine ⟨b.equivFun.symm c, ?_⟩
    apply b.equivFun.injective
    funext i
    simp only [map_sub, map_sum, map_smul, LinearEquiv.apply_symm_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hc' i
  · intro m hm
    apply b.equivFun.injective
    funext i
    show b.equivFun m i = b.equivFun 0 i
    rw [map_zero]
    show b.equivFun m i = 0
    apply hs
    intro n
    obtain ⟨z, hz⟩ := hm n
    refine ⟨b.equivFun z i, ?_⟩
    rw [hz, map_smul]
    rfl

end GlobalTheory
