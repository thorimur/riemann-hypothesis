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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcdeg_degreeOf_X_le {σ R : Type*} [CommRing R] [DecidableEq σ] (i j : σ) :
    degreeOf i (X j : MvPolynomial σ R) ≤ if j = i then 1 else 0 := by
  rw [degreeOf_eq_sup]
  refine Finset.sup_le fun m hm => ?_
  have hm' : m ∈ (monomial (Finsupp.single j 1) (1 : R)).support := hm
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset hm')
  rw [Finsupp.single_apply]

theorem lcdeg_degreeOf_aeval_le {σ τ R : Type*} [CommRing R] (f : σ → MvPolynomial τ R)
    (p : MvPolynomial σ R) (c : τ) (d : ℕ)
    (h : ∀ m ∈ p.support, ∑ v ∈ m.support, m v * degreeOf c (f v) ≤ d) :
    degreeOf c (aeval f p) ≤ d := by
  classical
  rw [aeval_def, eval₂_eq]
  have key : ∀ m ∈ p.support, degreeOf c (algebraMap R (MvPolynomial τ R) (coeff m p) *
      ∏ v ∈ m.support, f v ^ m v) ≤ d := by
    intro m hm
    rw [algebraMap_eq]
    refine (degreeOf_C_mul_le _ _ _).trans ?_
    exact (degreeOf_prod_le _ _ _).trans
      ((Finset.sum_le_sum fun v _ => degreeOf_pow_le _ _ _).trans (h m hm))
  clear h
  generalize p.support = s at key ⊢
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (degreeOf_add_le _ _ _).trans (max_le (key a (Finset.mem_insert_self _ _))
      (ih fun m hm => key m (Finset.mem_insert_of_mem hm)))

end Formalism.GradedWeylDivisibility
