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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.AdjoinForm.adjoin_form :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    {d : ℕ},
    (0 : ℕ) < d → ∀ {x : E}, x ^ (2 : ℕ) = -(↑d : E) → ∀ y ∈ ℚ⟮x⟯, ∃ (s : ℚ) (t : ℚ), y = (↑s : E) + (↑t : E) * x := by
  intro E _ _ d _ x hx y hy
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have h : y ∈ (ℚ⟮x⟯).toSubalgebra := hy
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at h
  clear hy
  induction h using Algebra.adjoin_induction with
  | mem a ha =>
    rw [Set.mem_singleton_iff] at ha
    exact ⟨0, 1, by simp [ha]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ iha ihb =>
    obtain ⟨s, t, rfl⟩ := iha
    obtain ⟨s', t', rfl⟩ := ihb
    exact ⟨s + s', t + t', by push_cast; ring⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨s, t, rfl⟩ := iha
    obtain ⟨s', t', rfl⟩ := ihb
    exact ⟨s * s' - t * t' * d, s * t' + t * s', by push_cast; linear_combination (t * t' : E) * hx⟩
