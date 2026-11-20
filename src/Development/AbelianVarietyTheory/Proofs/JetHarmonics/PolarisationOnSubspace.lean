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

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem polarisation_on_subspace : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : V → Prop) (B T : V → V → ℂ), (∀ (a : ℂ) x y, S x → S y → S (x + a • y)) → (∀ (a : ℂ) x y, S x → S y → B (x + a • y) (x + a • y) = B x x + a * B y x + (starRingEnd ℂ) a * B x y + a * (starRingEnd ℂ) a * B y y) → (∀ (a : ℂ) x y, S x → S y → T (x + a • y) (x + a • y) = T x x + a * T y x + (starRingEnd ℂ) a * T x y + a * (starRingEnd ℂ) a * T y y) → (∀ x, S x → B x x = T x x) → ∀ x y, S x → S y → B x y = T x y := by
  intro V _ _ S B T hS hB hT hd x y hx hy
  have key : ∀ a : ℂ, a * B y x + (starRingEnd ℂ) a * B x y = a * T y x + (starRingEnd ℂ) a * T x y := by
    intro a
    have h := hd _ (hS a x y hx hy)
    rw [hB a x y hx hy, hT a x y hx hy, hd x hx, hd y hy] at h
    linear_combination h
  have h1 := key 1
  have h2 := key Complex.I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2
    - ((B y x - T y x - B x y + T x y) / 2) * Complex.I_mul_I

end GlobalTheory
