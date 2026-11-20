import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

theorem posDef_herm_norm_triangle :
    ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), Hm.PosDef →
      √(((a + b) ⬝ᵥ Hm.mulVec (star (a + b))).re) ≤
        √((a ⬝ᵥ Hm.mulVec (star a)).re) + √((b ⬝ᵥ Hm.mulVec (star b)).re) := by
  intro g Hm a b hH
  have hS := hH.posSemidef
  have key : ∀ x : Fin g → ℂ,
      @norm _ (Hm.toSeminormedAddCommGroup hS).toNorm (star x) = √((x ⬝ᵥ Hm.mulVec (star x)).re) := by
    intro x
    rw [@norm_eq_sqrt_re_inner ℂ _ _ (Hm.toSeminormedAddCommGroup hS) (Hm.toInnerProductSpace hS)]
    change √(RCLike.re ((Hm.mulVec (star x)) ⬝ᵥ star (star x))) = _
    rw [star_star, dotProduct_comm, RCLike.re_to_complex]
  have h := @norm_add_le _ (Hm.toSeminormedAddCommGroup hS).toSeminormedAddGroup (star a) (star b)
  rw [← star_add, key, key, key] at h
  exact h

end GlobalTheory
