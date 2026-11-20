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

theorem UpperTheory.Reformulated.B.Qi28.exists_extend.{u_1, u_2} :
    ∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ),
    RingHom.ker (Algebra.algebraMap R A) ≤ RingHom.ker ev → ∃ (χ : A →+* ℂ), χ.comp (Algebra.algebraMap R A) = ev := by
  intro R A _ _ _ _ ev h
  haveI hP : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := A) (RingHom.ker ev) ⊥
    (by rw [← RingHom.ker_eq_comap_bot]; exact h)
  haveI : Q.LiesOver (RingHom.ker ev) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker ev) ℂ := (RingHom.kerLift ev).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker ev) ℂ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective ev)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker ev) (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : FaithfulSMul (R ⧸ RingHom.ker ev) (A ⧸ Q) := inferInstance
  haveI : IsDomain (R ⧸ RingHom.ker ev) := Ideal.Quotient.isDomain _
  haveI : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker ev) (A ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker ev) ℂ :=
    Module.isTorsionFree_iff_faithfulSMul.2 ‹_›
  let φ : (A ⧸ Q) →ₐ[R ⧸ RingHom.ker ev] ℂ := IsAlgClosed.lift
  refine ⟨(φ : (A ⧸ Q) →+* ℂ).comp (Ideal.Quotient.mk Q), ?_⟩
  ext r
  exact φ.commutes (Ideal.Quotient.mk (RingHom.ker ev) r)
