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

theorem UpperTheory.Reformulated.B.Qj2.exists_sum_tmul :
    ∀ {R O B σ : Type} [inst : CommRing R]
    [inst_1 : AddCommGroup O] [inst_2 : _root_.Module R O] [inst_3 : AddCommGroup B] [inst_4 : _root_.Module R B]
    [inst_5 : Fintype σ] (ω : Module.Basis σ R O) (x : TensorProduct R O B),
    ∃ (y : σ → B), x = ∑ s : σ, (ω : σ → O) s ⊗ₜ[R] y s := by
  intro R O B σ _ _ _ _ _ _ ω x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o b =>
    refine ⟨fun s => ω.repr o s • b, ?_⟩
    conv_lhs => rw [← ω.sum_repr o]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun s _ => TensorProduct.smul_tmul _ _ _
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    refine ⟨y₁ + y₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => (TensorProduct.tmul_add _ _ _).symm
