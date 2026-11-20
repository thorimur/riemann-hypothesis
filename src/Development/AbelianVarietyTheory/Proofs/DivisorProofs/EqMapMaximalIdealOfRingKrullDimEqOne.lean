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
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
open IsLocalRing

namespace GlobalTheory

theorem eq_map_maximalIdeal_of_ringKrullDim_eq_one (R A : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Flat R A]
    (p : Ideal A) [p.IsPrime] :
    (maximalIdeal R).map (algebraMap R A) ≤ p → ringKrullDim (Localization.AtPrime p) = 1 →
      IsDomain (A ⧸ (maximalIdeal R).map (algebraMap R A)) →
      p = (maximalIdeal R).map (algebraMap R A) := by
  intro hle hdim hdom
  set I := (maximalIdeal R).map (algebraMap R A) with hI
  haveI : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).1 hdom
  have hp1 : p.height = 1 := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
    rw [hdim] at h
    exact_mod_cast h.symm
  haveI : p.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hp1]; exact ENat.one_ne_top
  haveI : I.FiniteHeight := Ideal.finiteHeight_of_le hle (Ideal.IsPrime.ne_top ‹_›)

  have hIne : I ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hmem : ϖ ∈ maximalIdeal R := by
      rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
    have hreg : IsSMulRegular A ϖ :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
    have hne : algebraMap R A ϖ ≠ 0 := by
      intro h0
      have : ϖ • (1 : A) = ϖ • (0 : A) := by rw [Algebra.smul_def, mul_one, h0, smul_zero]
      exact one_ne_zero (hreg this)
    intro hbot
    apply hne
    have : algebraMap R A ϖ ∈ I := Ideal.mem_map_of_mem _ hmem
    rw [hbot] at this
    exact (Ideal.mem_bot).1 this
  have hIh : 1 ≤ I.height := by
    rw [ENat.one_le_iff_ne_zero]
    intro h0
    exact hIne (Ideal.height_eq_zero_iff_eq_bot.1 h0)
  exact (Ideal.eq_of_le_of_height_le I hle (by rw [hp1]; exact hIh)).symm

end GlobalTheory
