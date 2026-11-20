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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Div

theorem exists_algHom_quotient_minimalPrime_injective (R K : Type) [CommRing R] [IsDomain R] [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K] (D : Type) [CommRing D] [Algebra R D] [Module.Flat R D] [Algebra.IsAlgebraic R D] (P : Ideal D) (hP : P ∈ minimalPrimes D) : ∃ em : D ⧸ P →ₐ[R] K, Function.Injective em := by
  haveI hPp : P.IsPrime := hP.1.1
  have hinj : Function.Injective (algebraMap R (D ⧸ P)) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    have hreg : IsSMulRegular D r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero h0)
    have hnz : algebraMap R D r ∈ nonZeroDivisors D := by
      rw [mem_nonZeroDivisors_iff_left]
      intro x hx
      apply hreg
      simp only [smul_zero]
      rw [Algebra.smul_def]; exact hx
    have hmem : algebraMap R D r ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hr
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) hmem hnz
  haveI : FaithfulSMul R (D ⧸ P) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective R K)
  haveI : Algebra.IsAlgebraic R (D ⧸ P) :=
    ⟨fun x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact (Algebra.IsAlgebraic.isAlgebraic (R := R) y).algHom (Ideal.Quotient.mkₐ R P)⟩
  haveI : Module.IsTorsionFree R (D ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective R K)
  let f : D ⧸ P →ₐ[R] K := IsAlgClosed.lift
  refine ⟨f, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨y, r, hr, hy⟩ : ∃ y : D ⧸ P, ∃ r : R, r ≠ 0 ∧ x * y = algebraMap R _ r := by
    obtain ⟨r, hr, y, hy⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) x).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
    exact ⟨y, r, hr, hy.symm⟩
  have := congrArg f hy
  rw [map_mul, hx, zero_mul, AlgHom.commutes] at this
  exact hr (IsFractionRing.injective R K (by rw [← this, map_zero]))

end GlobalTheory.Div
