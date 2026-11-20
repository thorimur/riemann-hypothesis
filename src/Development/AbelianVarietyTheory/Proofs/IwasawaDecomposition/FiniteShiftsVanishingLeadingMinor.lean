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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
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
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

theorem shift_minors_vanish_finite {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  classical
  let p : ℕ → Polynomial ℂ := fun k =>
    if hk : k ≤ n then (-(B.submatrix (Fin.castLE hk) (Fin.castLE hk))).charpoly else 1
  have key : ∀ (k : ℕ) (hk : k ≤ n) (s : ℂ),
      ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det
        = (p k).eval s := by
    intro k hk s
    simp only [p, dif_pos hk, Matrix.eval_charpoly]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.neg_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply,
      Fin.castLE_inj, smul_eq_mul, sub_neg_eq_add]
    split_ifs <;> ring
  have hp : ∀ k, p k ≠ 0 := by
    intro k
    by_cases hk : k ≤ n
    · simp only [p, dif_pos hk]; exact (Matrix.charpoly_monic _).ne_zero
    · simp [p, dif_neg hk]
  refine Set.Finite.subset
    ((Finset.range (n + 1)).finite_toSet.biUnion fun k _ =>
      Polynomial.finite_setOf_isRoot (hp k)) ?_
  intro s hs
  simp only [Set.mem_setOf_eq, not_forall, not_not] at hs
  obtain ⟨k, hk, h0⟩ := hs
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_setOf_eq]
  exact ⟨k, Nat.lt_succ_of_le hk, by rw [Polynomial.IsRoot, ← key k hk s, h0]⟩

end GlobalTheory
