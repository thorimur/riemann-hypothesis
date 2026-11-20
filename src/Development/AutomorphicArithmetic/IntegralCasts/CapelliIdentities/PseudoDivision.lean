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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

universe u

theorem UpperTheory.pseudo_division :
    ∀ (R : Type u) [CommRing R] (g p : Polynomial R), g ≠ 0 → ∃ (k : ℕ) (q r : Polynomial R), Polynomial.C (g.leadingCoeff ^ k) * p = g * q + r ∧ r.degree < g.degree := by
  intro R _ g p hg
  induction p using (Polynomial.degree_lt_wf (R := R)).induction with
  | _ p ih =>
    by_cases h : p.degree < g.degree
    · exact ⟨0, 0, p, by simp, h⟩
    · have hle : g.degree ≤ p.degree := not_lt.mp h
      have hp : p ≠ 0 := by
        rintro rfl
        rw [Polynomial.degree_zero, le_bot_iff, Polynomial.degree_eq_bot] at hle
        exact hg hle
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Polynomial.natDegree_le_natDegree hle)
      have hlt : (Polynomial.C g.leadingCoeff * p
          - g * Polynomial.monomial d p.leadingCoeff).degree < p.degree := by
        rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        obtain ⟨j, rfl⟩ : ∃ j, m = j + d := ⟨m - d, by omega⟩
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_mul_monomial]
        rcases Nat.eq_or_lt_of_le hm with he | hl
        · have hj : j = g.natDegree := by omega
          rw [← he, hj]
          exact sub_self _
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl,
            Polynomial.coeff_eq_zero_of_natDegree_lt (show g.natDegree < j by omega)]
          simp
      obtain ⟨k, q, r, he, hr⟩ := ih _ hlt
      refine ⟨k + 1, q + Polynomial.C (g.leadingCoeff ^ k) * Polynomial.monomial d p.leadingCoeff,
        r, ?_, hr⟩
      rw [pow_succ, Polynomial.C_mul]
      linear_combination he
