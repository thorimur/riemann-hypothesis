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
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

theorem ChartGram.det_eq_corner_mul_schur {K : Type*} [Field K] {e : ℕ}
    (M : Matrix (Fin (e + 1)) (Fin (e + 1)) K) (h : M 0 0 ≠ 0) :
    M.det = M 0 0 *
      (Matrix.of fun i j : Fin e => M i.succ j.succ - M i.succ 0 * M 0 j.succ / M 0 0).det := by
  set c : Fin (e + 1) → K := fun i => if i = 0 then 0 else -(M i 0 / M 0 0) with hc
  set B : Matrix (Fin (e + 1)) (Fin (e + 1)) K := Matrix.of fun i j => M i j + c i * M 0 j with hB
  have hdet : B.det = M.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [hc]) (fun i j => by simp [hB])
  rw [← hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin e, B i.succ 0 = 0 := by
    intro i
    simp only [hB, hc, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    field_simp
    ring
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero]
  congr 1
  · simp [hB, hc]
  · congr 1
    ext i j
    simp only [hB, hc, Matrix.submatrix_apply, Matrix.of_apply, Fin.succ_ne_zero, if_false]
    ring

end GroundTheory.Heights₂.Heights
