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

theorem UpperTheory.V.Th.fNil :
    ∀ (K S : Type) [CommRing K] [IsDomain K] [CommRing S] (f : K →+* S) (n N q : ℕ) (α : Fin n → K) (U : Fin n → S), (∀ k, (U k - f (α k)) ^ N = 0) → ¬ (∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (q : K) * α i') → (∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, (U i - U i') * (U i - (q : S) * U i')) ^ (2 * N) = 0 := by
  intro K S _ _ _ f n N q α U hU hne
  simp only [not_forall] at hne
  obtain ⟨i, i', hii', hα⟩ := hne
  have hcase : (U i - U i') ^ (2 * N) = 0 ∨ (U i - (q : S) * U i') ^ (2 * N) = 0 := by
    have ha : (U i - f (α i)) ^ N = 0 := hU i
    have hb : (U i' - f (α i')) ^ N = 0 := hU i'
    by_cases he : α i = α i'
    · left
      have hnb : (-(U i' - f (α i'))) ^ N = 0 := by rw [neg_pow, hb, mul_zero]
      have hx : U i - U i' = (U i - f (α i)) + -(U i' - f (α i')) := by
        rw [he]
        ring
      rw [hx]
      exact Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (Commute.all _ _) ha hnb
        (by omega)
    · right
      have hq : α i = (q : K) * α i' := by
        by_contra h'
        exact hα ⟨he, h'⟩
      have hnb : (-(q : S) * (U i' - f (α i'))) ^ N = 0 := by rw [mul_pow, hb, mul_zero]
      have hx : U i - (q : S) * U i' = (U i - f (α i)) + -(q : S) * (U i' - f (α i')) := by
        rw [hq, map_mul, map_natCast]
        ring
      rw [hx]
      exact Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero (Commute.all _ _) ha hnb
        (by omega)
  have hY : ((U i - U i') * (U i - (q : S) * U i')) ^ (2 * N) = 0 := by
    rw [mul_pow]
    rcases hcase with h | h
    · rw [h, zero_mul]
    · rw [h, mul_zero]
  have hdvd : (U i - U i') * (U i - (q : S) * U i') ∣
      ∏ j : Fin n, ∏ j' ∈ Finset.univ.erase j, (U j - U j') * (U j - (q : S) * U j') :=
    (Finset.dvd_prod_of_mem (fun j' => (U i - U j') * (U i - (q : S) * U j'))
      (Finset.mem_erase.2 ⟨hii'.symm, Finset.mem_univ _⟩)).trans
      (Finset.dvd_prod_of_mem
        (fun j => ∏ j' ∈ Finset.univ.erase j, (U j - U j') * (U j - (q : S) * U j'))
        (Finset.mem_univ i))
  exact zero_dvd_iff.1 (hY ▸ pow_dvd_pow_of_dvd hdvd (2 * N))
