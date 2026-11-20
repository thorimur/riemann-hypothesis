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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

namespace GlobalTheory.CompanionTheory.TyFin.Orth

theorem sum_inv_addChar_mul_left (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : K) :
    (∑ t : K, (ψ₀ (t * x))⁻¹) = if x = 0 then (Fintype.card K : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    have hbij : Function.Bijective (fun t : K => -(t * x)) := by
      refine ⟨fun a b h => ?_, fun b => ⟨-(b * x⁻¹), ?_⟩⟩
      · exact mul_right_cancel₀ hx (neg_injective h)
      · simp [hx]
    have h1 : (∑ t : K, (ψ₀ (t * x))⁻¹) = ∑ t : K, ψ₀ (-(t * x)) :=
      Finset.sum_congr rfl fun t _ => (AddChar.map_neg_eq_inv ψ₀ (t * x)).symm
    rw [h1, hbij.sum_comp (fun u => ψ₀ u)]
    exact AddChar.sum_eq_zero_of_ne_one hψ

theorem sum_inv_addChar_dot (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ)
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : Fin j → K) :
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹)
      = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by
  have h1 : ∀ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹ = ∏ i, (ψ₀ (r i * x i))⁻¹ := by
    intro r
    have hs : ∀ s : Finset (Fin j), ψ₀ (∑ i ∈ s, r i * x i) = ∏ i ∈ s, ψ₀ (r i * x i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    rw [hs, Finset.prod_inv_distrib]
  have h2 : (∑ r : Fin j → K, ∏ i, (ψ₀ (r i * x i))⁻¹)
      = ∏ i, ∑ t : K, (ψ₀ (t * x i))⁻¹ := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [h1]
  rw [h2]
  simp_rw [sum_inv_addChar_mul_left K ψ₀ hψ]
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem orth : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ),
    ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 :=
  fun K _ _ _ j ψ₀ hψ x => sum_inv_addChar_dot K j ψ₀ hψ x

end GlobalTheory.CompanionTheory.TyFin.Orth
