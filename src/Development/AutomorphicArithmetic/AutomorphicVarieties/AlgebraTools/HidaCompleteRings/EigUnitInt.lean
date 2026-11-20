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

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite
    {O K : Type*} [CommRing O] [Field K] [Algebra O K] {M : Type*} [AddCommGroup M] [Module O M]
    [Module.Finite O M] (T : Module.End O M) (μ : K) (y : K ⊗[O] M) (hy : y ≠ 0)
    (h : T.baseChange K y = μ • y) : IsIntegral O μ := by
  obtain ⟨p, hp, hT⟩ := LinearMap.exists_monic_and_aeval_eq_zero O T
  have key : ∀ q : Polynomial O,
      (Polynomial.aeval T q).baseChange K y = (Polynomial.aeval μ q) • y := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      rw [Polynomial.aeval_C, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
        LinearMap.baseChange_smul, LinearMap.baseChange_one, LinearMap.smul_apply,
        Module.End.one_apply, algebraMap_smul]
    | add p q hp hq =>
      rw [map_add, map_add, LinearMap.baseChange_add, LinearMap.add_apply, hp, hq, add_smul]
    | monomial n a ih =>
      rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval T), map_mul (Polynomial.aeval μ),
        Polynomial.aeval_X, Polynomial.aeval_X, LinearMap.baseChange_mul, Module.End.mul_apply,
        h, map_smul, ih, smul_smul, mul_comm]
  have h0 := key p
  rw [hT, LinearMap.baseChange_zero, LinearMap.zero_apply] at h0
  have h1 : Polynomial.aeval μ p = 0 := (smul_eq_zero.mp h0.symm).resolve_right hy
  exact ⟨p, hp, by rwa [Polynomial.aeval_def] at h1⟩

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] (U V e : Module.End O M), V * U * e = e → ∀ (μ : K) (y : K ⊗[O] M), y ≠ 0 → e.baseChange K y = y → U.baseChange K y = μ • y → μ ≠ 0 ∧ IsIntegral O μ ∧ IsIntegral O μ⁻¹ := by
  intro O K _ _ _ M _ _ _ U V e hVU μ y hy he hU
  have h1 : μ • V.baseChange K y = y := by
    have h := congrArg (fun f : Module.End O M => f.baseChange K y) hVU
    simp only [LinearMap.baseChange_mul, Module.End.mul_apply] at h
    rwa [he, hU, map_smul] at h
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at h1
    exact hy h1.symm
  have h2 : V.baseChange K y = μ⁻¹ • y := by
    conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ hμ, one_smul]
  exact ⟨hμ, UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite U μ y hy hU,
    UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigenvalue_integral_of_finite V μ⁻¹ y hy h2⟩
