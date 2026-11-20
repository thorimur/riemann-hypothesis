import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
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
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_mul_eq_zero_dom : ∀ f g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → (∀ τ, f τ * g τ = 0) → f = 0 ∨ g = 0 := by
  intro f g hf hg hfg
  have hF := (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hG := (UpperHalfPlane.mdifferentiable_iff.mp hg).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hne : ({z : ℂ | 0 < z.im}).Nonempty := ⟨Complex.I, by simp⟩
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hF hG (fun z _ => by simp [Function.comp_apply, hfg]) hU with h | h
  · left
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this
  · right
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
