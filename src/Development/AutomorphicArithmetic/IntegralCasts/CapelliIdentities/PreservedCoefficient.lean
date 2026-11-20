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

private theorem coeff_mem_of_mem_maximalIdeal {O σ : Type} [CommRing O] [IsLocalRing O]
    {g : MvPowerSeries σ O} (hg : g ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O))
    (b : σ →₀ ℕ) :
    MvPowerSeries.coeff b g ∈ IsLocalRing.maximalIdeal O ^ (1 - Finsupp.degree b) := by
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, Nat.sub_zero, pow_one, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← MvPowerSeries.isUnit_iff_constantCoeff]
    exact hg
  · have h1 : Finsupp.degree b ≠ 0 := fun h => hb ((Finsupp.degree_eq_zero_iff b).1 h)
    have h2 : 1 - Finsupp.degree b = 0 := by omega
    rw [h2, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

theorem UpperTheory.Reformulated.B.PreservedCoefficient.pres_new_coeff :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : IsLocalRing O]
    (N : ℕ),
    ∀ h ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ N,
      ∀ (a : σ →₀ ℕ),
        (MvPowerSeries.coeff a : MvPowerSeries σ O → O) h ∈
          IsLocalRing.maximalIdeal O ^ (N - (Finsupp.degree : (σ →₀ ℕ) → ℕ) a) := by
  intro O σ _ _ N
  classical
  induction N with
  | zero =>
    intro h _ a
    rw [Nat.zero_sub, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ N ih =>
    intro h hh
    rw [pow_succ] at hh
    refine Submodule.mul_induction_on hh ?_ ?_
    · intro f hf g hg a
      rw [MvPowerSeries.coeff_mul]
      refine Submodule.sum_mem _ fun p hp => ?_
      have hsum : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree a := by
        rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hp]
      have hmul := Ideal.mul_mem_mul (ih f hf p.1) (coeff_mem_of_mem_maximalIdeal hg p.2)
      rw [← pow_add] at hmul
      exact Ideal.pow_le_pow_right (by omega) hmul
    · intro f g hf hg a
      rw [map_add]
      exact Submodule.add_mem _ (hf a) (hg a)
