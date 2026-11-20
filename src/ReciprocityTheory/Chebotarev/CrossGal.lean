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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Presheaf

open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem cxgal_exists_sf (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ p : ℚ[X], p ≠ 0 ∧ IsSplittingField ℚ K p := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField ℚ K
  by_cases h0 : p = 0
  · subst h0
    refine ⟨X, X_ne_zero, ?_⟩
    constructor
    · simp
    · have h := hp.adjoin_rootSet
      simp only [rootSet_zero, Algebra.adjoin_empty] at h
      rw [eq_top_iff, ← h]
      exact bot_le
  · exact ⟨p, h0, hp⟩

theorem isGalois_cyclotomicField (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (l : ℕ) [NeZero l] :
    IsGalois ℚ (CyclotomicField l K) := by
  obtain ⟨p, hp0, hp⟩ := cxgal_exists_sf K
  have : IsSplittingField K (CyclotomicField l K) ((X ^ l - 1 : ℚ[X]).map (algebraMap ℚ K)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one l K (CyclotomicField l K)
  have := IsSplittingField.mul (K := K) (L := CyclotomicField l K) p (X ^ l - 1) hp0
    (X_pow_sub_C_ne_zero (NeZero.pos l) 1)
  have : Normal ℚ (CyclotomicField l K) := Normal.of_isSplittingField (p * (X ^ l - 1))
  exact IsGalois.mk

end ReciprocityTheory.Cheb
