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
import Mathlib.RingTheory.PiTensorProduct
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

open Matrix

namespace Bl.FirstLemmaB

theorem goal1 {R : Type*} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R)
    (c : R) (hc : c ∈ nonZeroDivisors R) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) R)) :
    P * Q = c • (1 : Matrix (Fin n) (Fin n) R) := by
  have hdet : Q.det * P.det = c ^ n := by
    rw [← det_mul, h, det_smul, det_one, mul_one, Fintype.card_fin]
  have hcn : c ^ n ∈ nonZeroDivisors R := pow_mem hc n
  have hP : P.det ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply (mem_nonZeroDivisors_iff_right.mp hcn) x
    rw [← hdet, mul_comm Q.det P.det, ← mul_assoc, hx, zero_mul]
  have h1 : Q * P * P.adjugate = c • P.adjugate := by
    rw [h, smul_mul_assoc, Matrix.one_mul]
  have h2 : P.det • Q = c • P.adjugate := by
    rw [← h1, Matrix.mul_assoc, mul_adjugate, mul_smul_comm, Matrix.mul_one]
  have key : P.det • (P * Q) = P.det • (c • (1 : Matrix (Fin n) (Fin n) R)) := by
    calc P.det • (P * Q) = P * (P.det • Q) := (mul_smul_comm _ _ _).symm
      _ = P * (c • P.adjugate) := by rw [h2]
      _ = c • (P * P.adjugate) := mul_smul_comm _ _ _
      _ = c • (P.det • (1 : Matrix (Fin n) (Fin n) R)) := by rw [mul_adjugate]
      _ = P.det • (c • (1 : Matrix (Fin n) (Fin n) R)) := smul_comm _ _ _
  ext i j
  have hij := congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j) key
  simp only [Matrix.smul_apply, smul_eq_mul] at hij
  have hz : P.det * ((P * Q) i j - (c • (1 : Matrix (Fin n) (Fin n) R)) i j) = 0 := by
    rw [mul_sub, sub_eq_zero]
    simpa only [Matrix.smul_apply, smul_eq_mul] using hij
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_left.mp hP) _ hz)

end Bl.FirstLemmaB
