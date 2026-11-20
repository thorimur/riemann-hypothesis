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

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb

open Finset

theorem split {R : Type*} [CommRing R] (π q l : R) (hq : q = π + l) (e B r : ℕ) :
    π ^ (r + 1) * q ^ (e * (r + 1)) =
      (∑ k ∈ (range (r + 1)).filter (fun k => k + e * (r + 1) < B),
        (-1 : R) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * π * q ^ (k + e * (r + 1))) +
      π * q ^ B * ∑ k ∈ (range (r + 1)).filter (fun k => ¬ k + e * (r + 1) < B),
        (-1 : R) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * q ^ (k + e * (r + 1) - B) := by
  have hπ : π = q + (-l) := by rw [hq]; ring
  have h1 : π ^ (r + 1) * q ^ (e * (r + 1)) = π * q ^ (e * (r + 1)) * (q + (-l)) ^ r := by
    rw [← hπ]; ring
  rw [h1, add_pow, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not (range (r + 1))
    (fun k => k + e * (r + 1) < B), Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow]
    ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : B ≤ k + e * (r + 1) := by
      simp only [Finset.mem_filter] at hk
      omega
    have hq' : q ^ (k + e * (r + 1)) = q ^ B * q ^ (k + e * (r + 1) - B) := by
      rw [← pow_add]; congr 1; omega
    rw [neg_pow]
    calc π * q ^ (e * (r + 1)) * (q ^ k * ((-1) ^ (r - k) * l ^ (r - k)) * (r.choose k : R))
        = (-1) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * π * q ^ (k + e * (r + 1)) := by ring
      _ = π * q ^ B * ((-1) ^ (r - k) * (r.choose k : R) * l ^ (r - k) * q ^ (k + e * (r + 1) - B)) := by
        rw [hq']; ring

theorem count (e B r k : ℕ) (he : 1 ≤ e) (hk : k ≤ r) (hB : k + e * (r + 1) < B) (σ : ℝ)
    (hσ : (B : ℝ) / e ≤ σ) : ((r + 1 : ℕ) : ℝ) * (e + 1) / e ≤ σ + (r - k : ℕ) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : ((r - k : ℕ) : ℝ) = (r : ℝ) - k := by rw [Nat.cast_sub hk]
  have hB' : (k : ℝ) + e * (r + 1) + 1 ≤ B := by exact_mod_cast hB
  rw [h1, div_le_iff₀ he0]
  have h2 : (B : ℝ) ≤ σ * e := by rwa [div_le_iff₀ he0] at hσ
  push_cast
  have hkr : (k : ℝ) ≤ r := by exact_mod_cast hk
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  nlinarith [mul_nonneg (sub_nonneg.2 hkr) (sub_nonneg.2 he1)]

end Formalism.MainNotions.N.FrobeniusPowerSeries.DYAb
