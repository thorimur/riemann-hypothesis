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
import Mathlib.Tactic.Monotonicity.Lemmas
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

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem grid_sqrt_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i))
    (n : Fin K → Fin (d + 1)) :
    Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  have hmap : ∀ h : ℝ → ℝ,
      ((List.ofFn fun a => grid a (n a)).map h).prod = ∏ a, h (grid a (n a)) := by
    intro h
    rw [List.map_ofFn, List.prod_ofFn]
    rfl
  simp only [hmap]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  have hle : ∏ a, nn (grid a (n a)) * nn (grid a (n a) + 1) / Q (grid a (n a)) ≤
      ∏ _a : Fin K, β ^ 2 := by
    apply Finset.prod_le_prod
    · intro a _
      have h := hpos a (n a)
      exact div_nonneg (mul_nonneg h.1.le h.2.1.le) h.2.2.le
    · intro a _
      rw [div_le_iff₀ (hpos a (n a)).2.2]
      exact hb a (n a)
  calc _ ≤ Real.sqrt (∏ _a : Fin K, β ^ 2) := Real.sqrt_le_sqrt hle
    _ = β ^ K := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, pow_mul',
        Real.sqrt_sq (pow_nonneg hβ K)]

theorem grid_sum_le {K d : ℕ} (grid c : Fin K → Fin (d + 1) → ℝ) (nn Q : ℝ → ℝ) (β : ℝ)
    (hβ : 0 ≤ β)
    (hc : ∀ a, ∑ i, |c a i| ≤ 1)
    (hpos : ∀ a i, 0 < nn (grid a i) ∧ 0 < nn (grid a i + 1) ∧ 0 < Q (grid a i))
    (hb : ∀ a i, nn (grid a i) * nn (grid a i + 1) ≤ β ^ 2 * Q (grid a i)) :
    ∑ n : Fin K → Fin (d + 1), |∏ a, c a (n a)| *
      Real.sqrt (((List.ofFn fun a => grid a (n a)).map nn).prod *
        ((List.ofFn fun a => grid a (n a)).map fun y => nn (y + 1)).prod /
        ((List.ofFn fun a => grid a (n a)).map Q).prod) ≤ β ^ K := by
  calc _ ≤ ∑ n : Fin K → Fin (d + 1), |∏ a, c a (n a)| * β ^ K := by
        apply Finset.sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_left (grid_sqrt_le grid nn Q β hβ hpos hb n) (abs_nonneg _)
    _ = (∏ a, ∑ i, |c a i|) * β ^ K := by
        rw [← Finset.sum_mul, Fintype.prod_sum]
        simp only [Finset.abs_prod]
    _ ≤ 1 * β ^ K := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hβ K)
        apply Finset.prod_le_one
        · intro a _
          exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
        · intro a _
          exact hc a
    _ = β ^ K := one_mul _

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
