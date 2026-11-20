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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

universe u_1 u_2

namespace Bl.FirstLemmaA

theorem goal1 :
  ∀ {B : Type u_1} [inst : CommRing.{u_1} B] {ι : Type u_2} (s : Finset.{u_2} ι) (v : ι → Polynomial.{u_1} B)
  (d : ι → Nat),
  (∀ (i : ι), LE.le.{0} (Polynomial.natDegree.{u_1} (v i)) 1) →
    And
      (LE.le.{0}
        (Polynomial.natDegree.{u_1} (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (v i) (d i)))
        (Finset.sum.{u_2, 0} s fun (i : ι) ↦ d i))
      (Eq.{u_1 + 1}
        (Polynomial.coeff.{u_1} (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (v i) (d i))
          (Finset.sum.{u_2, 0} s fun (i : ι) ↦ d i))
        (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ HPow.hPow.{u_1, 0, u_1} (Polynomial.coeff.{u_1} (v i) 1) (d i))) := by
  intro B _ ι s v d hv
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih
    have hA : (v a ^ d a).natDegree ≤ d a := by
      simpa using Polynomial.natDegree_pow_le_of_le (d a) (hv a)
    have hc : (v a ^ d a).coeff (d a) = (v a).coeff 1 ^ d a := by
      simpa using Polynomial.coeff_pow_of_natDegree_le (m := d a) (hv a)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨Polynomial.natDegree_mul_le.trans (add_le_add hA h1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hA h1, hc, h2]

end Bl.FirstLemmaA
