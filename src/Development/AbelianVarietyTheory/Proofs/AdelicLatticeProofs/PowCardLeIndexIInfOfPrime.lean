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
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_card_le_index_iInf_of_prime :
    ∀ (p : ℕ) (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), p.Prime →
      (∀ (i : ι) (x : G), x ^ p ∈ K i) → (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) →
      (⨅ i, K i).index ≠ 0 → p ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro p G ι _ _ K hp hpow hx hind
  classical
  choose x hx1 hx2 using hx
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (G ⧸ (⨅ i, K i)) := Nat.finite_of_card_ne_zero hind
  have hord : ∀ j, orderOf (QuotientGroup.mk' (K j) (x j)) = p := by
    intro j
    apply orderOf_eq_prime
    · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hpow j _
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact hx1 j
  have hprod : ∀ (n : ι → Fin p) (j : ι),
      QuotientGroup.mk' (K j) (∏ i, x i ^ (n i : ℕ)) = (QuotientGroup.mk' (K j) (x j)) ^ (n j : ℕ) := by
    intro n j
    rw [map_prod, Finset.prod_eq_single j]
    · rw [map_pow]
    · intro i _ hij
      rw [map_pow]
      have : QuotientGroup.mk' (K j) (x i) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx2 i j (Ne.symm hij)
      rw [this, one_pow]
    · intro h
      exact absurd (Finset.mem_univ j) h
  let f : (ι → Fin p) → G ⧸ (⨅ i, K i) := fun n => QuotientGroup.mk (∏ i, x i ^ (n i : ℕ))
  have hf : Function.Injective f := by
    intro n m h
    have h1 := QuotientGroup.eq.1 h
    funext j
    have h2 := Subgroup.mem_iInf.1 h1 j
    have h3 : QuotientGroup.mk' (K j) (∏ i, x i ^ (n i : ℕ))
        = QuotientGroup.mk' (K j) (∏ i, x i ^ (m i : ℕ)) := QuotientGroup.eq.2 h2
    rw [hprod, hprod] at h3
    apply Fin.ext
    refine pow_injOn_Iio_orderOf ?_ ?_ h3
    · rw [hord]; exact (n j).2
    · rw [hord]; exact (m j).2
  have := Nat.card_le_card_of_injective f hf
  simpa [Subgroup.index] using this

end GlobalTheory.CNorm
