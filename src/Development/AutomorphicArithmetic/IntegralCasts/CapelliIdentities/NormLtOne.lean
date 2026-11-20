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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace UpperTheory.Reformulated.B.NormLtOne

theorem norm_lt_one {l : ℕ} [Fact l.Prime] {O R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing R] [IsLocalRing R] [Algebra O R]
    (y : R →ₐ[O] PadicAlgCl l) (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) : ‖y a‖ < 1 := by
  by_contra hx
  rw [not_lt] at hx
  have hx0 : y a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact absurd hx (by norm_num)
  have hu : ‖(y a)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have hint : IsIntegral ℚ_[l] (y a)⁻¹ := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly ℚ_[l] (y a)⁻¹).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] (y a)⁻¹).coeff n‖ ≤ 1 := by
    rw [← spectralValue_le_one_iff hmon]
    exact hu
  have hz := minpoly.aeval ℚ_[l] (y a)⁻¹
  generalize minpoly ℚ_[l] (y a)⁻¹ = P at hmon hc hz
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hz
  let c : ℕ → ℤ_[l] := fun i => ⟨P.coeff i, hc i⟩
  have hr : (∑ i ∈ Finset.range P.natDegree,
      algebraMap O R (algebraMap ℤ_[l] O (c i)) * a ^ (P.natDegree - i)) ∈ IsLocalRing.maximalIdeal R := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ha _ ?_)
    have := Finset.mem_range.mp hi
    omega
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem hr)
  apply (hunit.map y).ne_zero
  have hz' := congrArg (· * y a ^ P.natDegree) hz
  simp only [zero_mul, add_mul, Finset.sum_mul] at hz'
  rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow] at hz'
  rw [sub_neg_eq_add, map_add, map_one, map_sum, add_comm, ← hz']
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := (Finset.mem_range.mp hi).le
  rw [map_mul, map_pow, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), Algebra.smul_def, mul_assoc,
    pow_sub₀ _ hx0 hi', inv_pow, mul_comm (y a ^ P.natDegree)]
  rfl

end UpperTheory.Reformulated.B.NormLtOne
