import Mathlib.Algebra.Algebra.Epi
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rh

theorem epi : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B], (∀ b : B, b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) → Function.Surjective (algebraMap A B) := by
  intro A B _ _ _ _ h
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.mp
    ((Algebra.isEpi_iff_forall_one_tmul_eq A B).mpr fun b => (h b).symm)

theorem eq_of_prod_eq {T : Type} [Fintype T] (f g : T → NNReal) (hle : ∀ t, f t ≤ g t)
    (h : ∏ t, f t = ∏ t, g t) (h0 : ∏ t, f t ≠ 0) (t : T) : f t = g t := by
  by_contra hne
  have hpos : ∀ i ∈ Finset.univ, 0 < f i := fun i _ =>
    pos_iff_ne_zero.mpr ((Finset.prod_ne_zero_iff.mp h0) i (Finset.mem_univ i))
  have hlt := Finset.prod_lt_prod hpos (fun i _ => hle i)
    ⟨t, Finset.mem_univ t, lt_of_le_of_ne (hle t) hne⟩
  exact hlt.ne h

theorem grcount : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s := by
  intro T S _ _ a b ha hb x D d r cA cN cO hcN hxD hD hx hA hd hr hdx hOa
  have hab : a * b ≠ 0 := (Nat.mul_pos ha hb).ne'
  have hX : ∏ t, ∏ s, x t s = ∏ t, ∏ s, D t s := by
    rw [hD]
    exact (pow_left_inj₀ (by positivity) (by positivity) hab).mp (hx.trans hA.symm)
  have hX0 : ∏ t, ∏ s, x t s ≠ 0 := by
    intro h0
    rw [h0, zero_pow hab] at hx
    exact pow_ne_zero 2 hcN hx.symm
  have hrow : ∀ t, ∏ s, x t s = ∏ s, D t s :=
    PositivityTheory.HtPt.Rh.eq_of_prod_eq (fun t => ∏ s, x t s) (fun t => ∏ s, D t s)
      (fun t => Finset.prod_le_prod' fun s _ => hxD t s) hX hX0
  have hrow0 : ∀ t, ∏ s, x t s ≠ 0 := fun t =>
    (Finset.prod_ne_zero_iff.mp hX0) t (Finset.mem_univ t)
  have hxD' : ∀ t s, D t s = x t s := fun t s =>
    (PositivityTheory.HtPt.Rh.eq_of_prod_eq (x t) (D t) (hxD t) (hrow t) (hrow0 t) s).symm
  have hO : cO = ∏ t, ∏ s, d t s := by
    rw [hdx]
    apply (pow_left_inj₀ (by positivity) (by positivity) ha.ne').mp
    rw [hOa, ← pow_mul, mul_comm b a, hx]
  have hcol : ∏ s, ∏ t, d t s = ∏ s, r s := by
    rw [hr, hO, Finset.prod_comm]
  have hcol0 : ∏ s, ∏ t, d t s ≠ 0 := by
    rw [Finset.prod_comm, hdx]
    exact pow_ne_zero _ hX0
  exact ⟨hxD', PositivityTheory.HtPt.Rh.eq_of_prod_eq (fun s => ∏ t, d t s) r hd hcol hcol0⟩

end PositivityTheory.HtPt.Rh
