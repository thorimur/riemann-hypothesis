import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem sum_addChar_ofMul_mul_ofMul_inv (G : Type) [CommGroup G] [Fintype G] [DecidableEq G]
    (a b : G) :
    ∑ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      if a = b then (Fintype.card G : ℂ) else 0 := by
  have h : ∀ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul a) * ψ (Additive.ofMul b⁻¹) =
      ψ (Additive.ofMul (a * b⁻¹)) := by
    intro ψ
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul]
  simp_rw [h]
  rw [AddChar.sum_apply_eq_ite]
  have hc : Fintype.card (Additive G) = Fintype.card G :=
    Fintype.card_congr Additive.ofMul.symm
  simp only [hc, ofMul_eq_zero, mul_inv_eq_one]

end GlobalTheory.CompanionTheory.PartialZeta
