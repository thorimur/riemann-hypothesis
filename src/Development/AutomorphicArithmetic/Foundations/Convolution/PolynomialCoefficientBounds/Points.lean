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

open MvPolynomial Filter Topology

theorem UpperTheory.ConvolutionTheory.FX.separate_points :
    ∀ (σ B : Type) [Fintype B] (x : σ → ℂ) (y : B → σ → ℂ), (∀ s, y s ≠ x) → ∃ p : MvPolynomial σ ℂ, eval x p = 1 ∧ ∀ s, eval (y s) p = 0 := by
  intro σ B _ x y h
  classical
  have h1 : ∀ s, ∃ i, y s i ≠ x i := fun s => Function.ne_iff.mp (h s)
  choose i hi using h1
  refine ⟨∏ s, C (x (i s) - y s (i s))⁻¹ * (X (i s) - C (y s (i s))), ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_eq_one fun s _ => ?_
    have hne : x (i s) - y s (i s) ≠ 0 := sub_ne_zero.mpr (hi s).symm
    rw [map_mul, map_sub, eval_C, eval_C, eval_X, inv_mul_cancel₀ hne]
  · intro s
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    rw [map_mul, map_sub, eval_C, eval_C, eval_X, sub_self, mul_zero]
