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
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem finite_subring_common_denominator :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (S : Finset Ω),
      ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Subring.closure (S : Set Ω),
        ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x) := by
  intro Ω _ _ _ S
  have hZQ : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have hZ : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ ℚ Ω
  obtain ⟨y, hy0, hy⟩ := Algebra.IsAlgebraic.exists_integral_multiples (R := ℤ) S
  set D : ℕ := y.natAbs with hDdef
  refine ⟨D, Int.natAbs_pos.mpr hy0, ?_⟩
  have hDint : ∀ j : ℕ, IsIntegral ℤ ((D : Ω) ^ j) := by
    intro j
    have h : ((D : Ω) ^ j) = algebraMap ℤ Ω ((D : ℤ) ^ j) := by simp
    rw [h]
    exact isIntegral_algebraMap
  let T : Subring Ω :=
    { carrier := {x | ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * x)}
      mul_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have : (D : Ω) ^ (i + j) * (a * b) = ((D : Ω) ^ i * a) * ((D : Ω) ^ j * b) := by ring
        rw [this]; exact hi.mul hj
      one_mem' := ⟨0, by simpa using (isIntegral_one : IsIntegral ℤ (1 : Ω))⟩
      add_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have : (D : Ω) ^ (i + j) * (a + b) =
            (D : Ω) ^ j * ((D : Ω) ^ i * a) + (D : Ω) ^ i * ((D : Ω) ^ j * b) := by ring
        rw [this]; exact ((hDint j).mul hi).add ((hDint i).mul hj)
      zero_mem' := ⟨0, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : Ω))⟩
      neg_mem' := by
        rintro a ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have : (D : Ω) ^ i * -a = -((D : Ω) ^ i * a) := by ring
        rw [this]; exact hi.neg }
  have hST : (S : Set Ω) ⊆ T := by
    intro x hx
    refine ⟨1, ?_⟩
    have hx' := hy x hx
    rw [pow_one]
    rcases Int.natAbs_eq y with h | h
    · have e : y • x = (D : Ω) * x := by
        rw [zsmul_eq_mul]; congr 1; rw [h]; simp [hDdef]
      rw [← e]; exact hx'
    · have e : y • x = -((D : Ω) * x) := by
        rw [zsmul_eq_mul, h]; simp [hDdef]
      have := hx'.neg
      rw [e, neg_neg] at this
      exact this
  intro x hx
  exact (Subring.closure_le.mpr hST) hx

end GlobalTheory
