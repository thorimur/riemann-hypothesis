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

universe u_1 u_2

namespace Bl.FirstBlockLemmaA

theorem goal1 :
  ∀ {k : Type u_1} [inst : Field.{u_1} k] {σ : Type u_2} [Fintype.{u_2} σ] (H : MvPolynomial.{u_2, u_1} σ k) (d : Nat),
  (∀ (m : Finsupp.{u_2, 0} σ Nat),
      Membership.mem.{u_2, u_2} (MvPolynomial.support.{u_1, u_2} H) m →
        Eq.{1} (DFunLike.coe.{max 1 (u_2 + 1), max 1 (u_2 + 1), 1} Finsupp.degree.{u_2, 0} m) d) →
    ∀ (c : k) (v : σ → k),
      Eq.{u_1 + 1}
        (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1), u_1 + 1}
          (MvPolynomial.eval.{u_1, u_2} (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} c v)) H)
        (HMul.hMul.{u_1, u_1, u_1} (HPow.hPow.{u_1, 0, u_1} c d)
          (DFunLike.coe.{max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1), u_1 + 1} (MvPolynomial.eval.{u_1, u_2} v) H)) := by
  intro k _ σ _ H d h c v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [← h m hm, Finsupp.degree_eq_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end Bl.FirstBlockLemmaA
