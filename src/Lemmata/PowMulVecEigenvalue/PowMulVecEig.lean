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

namespace Bl.PowMulVecEigenvalue

private lemma pow_mulVec_eig {S : Type u_1} [CommRing S] {n : Type u_2} [Fintype n] [DecidableEq n]
    (Q : Matrix n n S) (μ : S) (v : n → S) (h : Q.mulVec v = μ • v) (k : ℕ) :
    (Q ^ k).mulVec v = μ ^ k • v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']

theorem goal1 :
  ∀ {S : Type u_1} [inst : CommRing.{u_1} S] {n : Type u_2} [inst_1 : Fintype.{u_2} n] [inst_2 : DecidableEq.{u_2 + 1} n]
  (Q : Matrix.{u_2, u_2, u_1} n n S) (μ : S) (v : n → S),
  Eq.{max (u_1 + 1) (u_2 + 1)} (Matrix.mulVec.{u_1, u_2, u_2} Q v) (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2} μ v) →
    ∀ (p : Polynomial.{0} Int),
      Eq.{max (u_1 + 1) (u_2 + 1)}
        (Matrix.mulVec.{u_1, u_2, u_2}
          (DFunLike.coe.{max (max (u_1 + 1) (u_2 + 1)) 1, 1, max (u_1 + 1) (u_2 + 1)}
            (Polynomial.aeval.{0, max u_1 u_2} Q) p)
          v)
        (HSMul.hSMul.{u_1, max u_1 u_2, max u_1 u_2}
          (DFunLike.coe.{max (u_1 + 1) 1, 1, u_1 + 1} (Polynomial.aeval.{0, u_1} μ) p) v) := by
  intro S _ n _ _ Q μ v h p
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, pow_mulVec_eig Q μ v h i, smul_assoc]

end Bl.PowMulVecEigenvalue
