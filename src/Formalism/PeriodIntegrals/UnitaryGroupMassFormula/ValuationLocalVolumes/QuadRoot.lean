import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

open Polynomial IsLocalRing

namespace PI.OmVf

theorem quad_root {R : Type*} [CommRing R] [HenselianLocalRing R] (A B K : R) (hA : A ∈ maximalIdeal R)
    (hB : IsUnit B) : ∃ s : R, A * s ^ 2 + B * s + K = 0 := by
  obtain ⟨u, hu⟩ := hB.exists_right_inv
  have haK : A * u * u * K ∈ maximalIdeal R := by
    have h1 : A * u * u * K = A * (u * u * K) := by ring
    rw [h1]; exact Ideal.mul_mem_right _ _ hA
  obtain ⟨w, hwr, hwm⟩ := HenselianLocalRing.is_henselian
    (X ^ 2 + X + Polynomial.C (A * u * u * K)) (by monicity!) 0
    (by simpa using haK) (by simp)
  have hw : w ^ 2 + w + A * u * u * K = 0 := by simpa using hwr
  have hwm' : w ∈ maximalIdeal R := by simpa using hwm
  have hunit : IsUnit (1 + w) := by
    by_contra hn
    have h1 : 1 + w ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hn
    have h2 : (1 : R) ∈ maximalIdeal R := by
      have e : (1 : R) = (1 + w) - w := by ring
      rw [e]; exact Ideal.sub_mem _ h1 hwm'
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  refine ⟨-(u * K * v), ?_⟩
  linear_combination K * v ^ 2 * hw - K * (2 - v + ((1 + w) * v - 1)) * hv - K * v * hu

end PI.OmVf
