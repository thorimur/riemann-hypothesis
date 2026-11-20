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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.Qh19.trace_pow_eq_zero_of_le_dim.{u_1} :
    ∀ {K : Type u_1}
    [inst : Field K] (r : ℕ) (N : Matrix (Fin r) (Fin r) K),
    (∀ (k : ℕ), (1 : ℕ) ≤ k → k ≤ r → (N ^ k).trace = (0 : K)) → ∀ (k : ℕ), (1 : ℕ) ≤ k → (N ^ k).trace = (0 : K) := by
  intro K _ r N h k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hkr : k ≤ r
    · exact h k hk hkr
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 + r := ⟨k - r - 1, by omega⟩
      have hd : N.charpoly.natDegree = r := by
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      have hc : N.charpoly.coeff r = 1 := by
        have := (Matrix.charpoly_monic N).coeff_natDegree
        rwa [hd] at this
      have hCH := Matrix.aeval_self_charpoly N
      rw [Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ, hc, one_smul] at hCH
      have h2 := congrArg (fun A => Matrix.trace (N ^ (m + 1) * A)) hCH
      simp only [mul_add, Finset.mul_sum, Matrix.mul_smul, ← pow_add, mul_zero, Matrix.trace_zero,
        Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul] at h2
      rw [Finset.sum_eq_zero, zero_add] at h2
      · exact h2
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [ih (m + 1 + i) (by omega) (by omega), smul_zero]
