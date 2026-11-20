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
import Mathlib.RingTheory.MvPowerSeries.Inverse
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

theorem UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff :
    ∀ {O σ : Type} [inst : CommRing O]
    [inst_1 : IsLocalRing O] (M : ℕ),
    ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ M,
      ∀ (n : σ →₀ ℕ),
        (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f ∈
          IsLocalRing.maximalIdeal O ^ (M - (Finsupp.degree : (σ →₀ ℕ) → ℕ) n) := by
  intro O σ _ _ M
  classical
  induction M with
  | zero =>
    intro f _ n
    simp
  | succ M ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb n
      rw [MvPowerSeries.coeff_mul]
      refine Ideal.sum_mem _ ?_
      rintro ⟨p, q⟩ hpq
      have hsum : p + q = n := by simpa using hpq
      have hdeg : Finsupp.degree p + Finsupp.degree q = Finsupp.degree n := by
        rw [← hsum, map_add]
      have hp := ih a ha p
      by_cases hq : q = 0
      · subst hq
        have hb0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) b ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
          intro hu
          exact hb (MvPowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hu))
        have hmul := Ideal.mul_mem_mul hp hb0
        rw [← pow_succ] at hmul
        exact Ideal.pow_le_pow_right (by omega) hmul
      · have hq' : Finsupp.degree q ≠ 0 := fun h => hq ((Finsupp.degree_eq_zero_iff q).mp h)
        exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) hp)
    · intro x y hx hy n
      rw [map_add]
      exact Ideal.add_mem _ (hx n) (hy n)
