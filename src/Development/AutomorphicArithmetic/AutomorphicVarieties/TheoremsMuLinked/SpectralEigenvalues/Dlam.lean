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
import Mathlib.RingTheory.MvPowerSeries.Derivative
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

open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.dlam :
    ∀ (O σ : Type) [CommRing O] [DecidableEq σ] (th : MvPowerSeries σ O →ₐ[O] O) (k : σ), ∃ d : MvPowerSeries σ O →ₗ[O] O, (∀ a b, d (a * b) = th a • d b + th b • d a) ∧ ∀ k', d (MvPowerSeries.X k') = if k = k' then 1 else 0 := by
  intro O σ _ _ th k
  refine ⟨th.toLinearMap ∘ₗ (MvPowerSeries.pderiv O k).toLinearMap, ?_, ?_⟩
  · intro a b
    show th (MvPowerSeries.pderiv O k (a * b)) =
      th a • th (MvPowerSeries.pderiv O k b) + th b • th (MvPowerSeries.pderiv O k a)
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, smul_eq_mul,
      smul_eq_mul]
  · intro k'
    show th (MvPowerSeries.pderiv O k (MvPowerSeries.X k')) = if k = k' then 1 else 0
    by_cases h : k = k'
    · subst h
      rw [MvPowerSeries.pderiv_X_self, map_one, if_pos rfl]
    · rw [MvPowerSeries.pderiv_X_of_ne (Ne.symm h), map_zero, if_neg h]
