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
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
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
open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory

theorem span_psum_eq_span_esymm (N : ℕ) :
    Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) =
      Ideal.span ((fun k => esymm (Fin N) ℝ k) '' Set.Icc 1 N) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨k, ⟨hk1, hkN⟩, rfl⟩
    have he : ∀ j, 1 ≤ j → j ≤ N → esymm (Fin N) ℝ j ∈
        Ideal.span ((fun k => esymm (Fin N) ℝ k) '' Set.Icc 1 N) :=
      fun j h1 h2 => Ideal.subset_span ⟨j, ⟨h1, h2⟩, rfl⟩
    show psum (Fin N) ℝ k ∈ Ideal.span _
    rw [psum_eq_mul_esymm_sub_sum (Fin N) ℝ k hk1]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (he k hk1 hkN)) ?_
    refine Ideal.sum_mem _ fun a ha => ?_
    rw [Finset.mem_filter, Set.mem_Ioo] at ha
    exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_left _ _ (he a.1 ha.2.1 (ha.2.2.le.trans hkN)))
  · rw [Ideal.span_le]
    rintro _ ⟨k, ⟨hk1, hkN⟩, rfl⟩
    have hp : ∀ j, 1 ≤ j → j ≤ N → psum (Fin N) ℝ j ∈
        Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) :=
      fun j h1 h2 => Ideal.subset_span ⟨j, ⟨h1, h2⟩, rfl⟩
    have h : (k : MvPolynomial (Fin N) ℝ) * esymm (Fin N) ℝ k ∈
        Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) := by
      rw [mul_esymm_eq_sum (Fin N) ℝ k]
      refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a ha => ?_)
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      exact Ideal.mul_mem_left _ _ (hp a.2 (by omega) (by omega))
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have h2 := Ideal.mul_mem_left _ (C (k : ℝ)⁻¹) h
    show esymm (Fin N) ℝ k ∈ Ideal.span _
    rwa [← mul_assoc, ← map_natCast (C : ℝ →+* MvPolynomial (Fin N) ℝ) k, ← map_mul,
      inv_mul_cancel₀ hk, map_one, one_mul] at h2

end GlobalTheory
