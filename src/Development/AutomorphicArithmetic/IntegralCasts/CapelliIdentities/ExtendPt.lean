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

theorem UpperTheory.Reformulated.B.Qi4.extendPt :
    ∀ (O Λ T K : Type) [inst : CommRing O] [inst_1 : CommRing Λ] [inst_2 : CommRing T]
    [inst_3 : Field K] [IsAlgClosed K] [inst_5 : Algebra O Λ] [inst_6 : Algebra O T] [inst_7 : Algebra Λ T]
    [IsScalarTower O Λ T] [inst_9 : Algebra O K] [Algebra.IsIntegral Λ T] (P : Ideal T) (y : Λ →ₐ[O] K),
    Ideal.comap (Algebra.algebraMap Λ T) P ≤ RingHom.ker y →
      ∃ (x : T →ₐ[O] K),
        P ≤ RingHom.ker x ∧ ∀ (a : Λ), (x : T → K) ((Algebra.algebraMap Λ T : Λ → T) a) = (y : Λ → K) a := by
  intro O Λ T K _ _ _ _ _ _ _ _ _ _ _ P y hP
  haveI hprime : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, hPQ, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker y) P hP
  have hker : ∀ a ∈ Q.comap (algebraMap Λ T), (y : Λ →+* K) a = 0 := by
    intro a ha
    rw [hQc] at ha
    exact ha
  let ybar : (Λ ⧸ Q.comap (algebraMap Λ T)) →+* K := Ideal.Quotient.lift _ (y : Λ →+* K) hker
  have hinj : Function.Injective ybar := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, hQc]
    exact ha
  letI : Algebra (Λ ⧸ Q.comap (algebraMap Λ T)) K := ybar.toAlgebra
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (Λ ⧸ Q.comap (algebraMap Λ T)) K :=
    FaithfulSMul.to_isTorsionFree _ _
  haveI hint : Algebra.IsIntegral (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.quotient
  haveI : Algebra.IsAlgebraic (Λ ⧸ Q.comap (algebraMap Λ T)) (T ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let z : (T ⧸ Q) →ₐ[Λ ⧸ Q.comap (algebraMap Λ T)] K := IsAlgClosed.lift
  have hz : ∀ a : Λ, z (Ideal.Quotient.mk Q (algebraMap Λ T a)) = y a := fun a =>
    z.commutes (Ideal.Quotient.mk _ a)
  refine ⟨{ (z : (T ⧸ Q) →+* K).comp (Ideal.Quotient.mk Q) with commutes' := fun o => ?_ }, ?_, hz⟩
  · have h := hz (algebraMap O Λ o)
    rw [← IsScalarTower.algebraMap_apply, y.commutes] at h
    exact h
  · intro t ht
    have h0 : Ideal.Quotient.mk Q t = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hPQ ht)
    show z (Ideal.Quotient.mk Q t) = 0
    rw [h0, map_zero]
