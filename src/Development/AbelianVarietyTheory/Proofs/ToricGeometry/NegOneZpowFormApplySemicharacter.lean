import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

theorem neg_one_zpow_form_apply_semicharacter :
    (∀ (X : Type) [AddCommGroup X] (E : LinearMap.BilinForm ℤ X) (w w' : X →ₗ[ℤ] X), (∀ x, E x x = 0) → w + w' = LinearMap.id → (∀ x y, E (w x) y = E x (w' y)) → ∀ x y, (-1 : ℂ) ^ E (x + y) (w (x + y)) = (-1) ^ E x (w x) * (-1) ^ E y (w y) * (-1) ^ E x y) := by
  intro X _ E w w' halt hsum hadj x y
  have hskew : ∀ a b, E a b = - E b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt] at h
    linarith
  have hy : w y + w' y = y := by
    have := LinearMap.congr_fun hsum y
    simpa using this
  have h1 : E x (w y) + E x (w' y) = E x y := by rw [← map_add, hy]
  have h2 : E y (w x) = - E x (w' y) := by rw [hskew, hadj]
  have h3 : E (x + y) (w (x + y))
      = E x (w x) + E y (w y) + E x y + 2 * (E x (w y) - E x y) := by
    simp only [map_add, LinearMap.add_apply]
    linarith
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  rw [h3, zpow_add₀ hne, zpow_add₀ hne, zpow_add₀ hne, _root_.zpow_mul]
  have h4 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
  rw [h4, _root_.one_zpow, mul_one]

end GlobalTheory
