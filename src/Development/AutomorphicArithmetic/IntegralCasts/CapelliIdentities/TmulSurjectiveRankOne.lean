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

theorem UpperTheory.Reformulated.B.Qj4.tmul_surjective_rank_one :
    ∀ {O T X : Type} [inst : CommRing O]
    [inst_1 : AddCommGroup T] [inst_2 : _root_.Module O T] [inst_3 : AddCommGroup X] [inst_4 : _root_.Module O X]
    (x₀ : X), (∀ (x : X), ∃ (c : O), x = c • x₀) → ∀ (m : TensorProduct O T X), ∃ (t : T), t ⊗ₜ[O] x₀ = m := by
  intro O T X _ _ _ _ _ x₀ h m
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.zero_tmul T x₀⟩
  | tmul t x =>
    obtain ⟨c, rfl⟩ := h x
    exact ⟨c • t, TensorProduct.smul_tmul c t x₀⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, TensorProduct.add_tmul s t x₀⟩
