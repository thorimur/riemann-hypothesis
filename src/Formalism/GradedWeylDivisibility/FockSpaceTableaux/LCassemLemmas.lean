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
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
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

open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem lcassem_sub_lt {σ R : Type*} [CommRing R] (o : MonomialOrder σ) {f g : MvPolynomial σ R}
    (hdeg : o.degree g = o.degree f) (hlc : o.leadingCoeff g = 1)
    (hne : f - o.leadingCoeff f • g ≠ 0) :
    o.degree (f - o.leadingCoeff f • g) ≺[o] o.degree f := by
  have hle : o.toSyn (o.degree (f - o.leadingCoeff f • g)) ≤ o.toSyn (o.degree f) := by
    refine (MonomialOrder.degree_sub_le (m := o)).trans (sup_le le_rfl ?_)
    rw [← hdeg]
    exact MonomialOrder.degree_smul_le (m := o)
  refine lt_of_le_of_ne hle fun heq => hne ?_

  have hd : o.degree (f - o.leadingCoeff f • g) = o.degree f := o.toSyn.injective heq
  have h1 : f.coeff (o.degree f) = o.leadingCoeff f := rfl
  have h2 : g.coeff (o.degree f) = 1 := by rw [← hdeg]; exact hlc
  rw [← o.coeff_degree_eq_zero_iff, hd, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, h1, h2,
    smul_eq_mul, mul_one, sub_self]

end Formalism.GradedWeylDivisibility
