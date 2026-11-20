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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
open MvPolynomial

namespace GlobalTheory

theorem coeff_allOnes_prod_one_add_mul {σ : Type} {L : ℕ} (m : Fin L → MvPolynomial σ ℂ)
    (a : MvPolynomial σ ℂ) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ))
      (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ ((∏ i, (1 + MvPolynomial.X (Sum.inl i) *
        MvPolynomial.rename Sum.inr (m i))) * MvPolynomial.rename Sum.inr a)) = (∏ i, m i) * a := by
  have hr : ∀ q : MvPolynomial σ ℂ, sumAlgEquiv ℂ (Fin L) σ (rename Sum.inr q) = C q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [sumAlgEquiv_C_inl]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p c hp => rw [map_mul, map_mul, hp, rename_X, sumAlgEquiv_X_inr, map_mul]
  have hx : ∀ i : Fin L, sumAlgEquiv ℂ (Fin L) σ (X (Sum.inl i)) = X i := fun i =>
    sumAlgEquiv_X_inl ℂ (Fin L) σ i
  have cmC : ∀ {τ : Type} (n : τ →₀ ℕ) (p : MvPolynomial τ (MvPolynomial σ ℂ)) (c : MvPolynomial σ ℂ),
      coeff n (p * C c) = coeff n p * c := by
    intro τ n p c; rw [mul_comm, coeff_C_mul, mul_comm]
  set e : Fin L →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ) with he
  have hmono : ∀ t : Finset (Fin L),
      coeff e (∏ i ∈ t, (X i * C (m i) : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) =
        if t = Finset.univ then ∏ i, m i else 0 := by
    intro t
    rw [Finset.prod_mul_distrib, ← map_prod, cmC]
    have hX : (∏ i ∈ t, (X i : MvPolynomial (Fin L) (MvPolynomial σ ℂ))) =
        monomial (∑ i ∈ t, Finsupp.single i 1) 1 := by
      rw [monomial_sum_one]; rfl
    rw [hX, coeff_monomial]
    by_cases ht : t = Finset.univ
    · subst ht
      have : (∑ i ∈ (Finset.univ : Finset (Fin L)), Finsupp.single i 1) = e := by
        ext j; simp [he, Finsupp.finset_sum_apply, Finsupp.single_apply]
      simp [this]
    · obtain ⟨j, hj⟩ : ∃ j, j ∉ t := by
        by_contra h; push_neg at h; exact ht (Finset.eq_univ_iff_forall.mpr h)
      have : (∑ i ∈ t, Finsupp.single i 1) ≠ e := by
        intro h
        have := congrArg (fun f => f j) h
        simp [he, Finsupp.finset_sum_apply, Finsupp.single_apply, hj] at this
      simp [this, ht]
  rw [map_mul, hr, cmC, map_prod]
  simp_rw [map_add, map_one, map_mul, hr, hx]
  rw [Finset.prod_one_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · rw [hmono]; simp
  · intro t _ ht; rw [hmono, if_neg ht]
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

end GlobalTheory
