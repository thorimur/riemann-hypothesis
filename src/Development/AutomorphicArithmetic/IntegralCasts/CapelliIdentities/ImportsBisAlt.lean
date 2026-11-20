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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

theorem UpperTheory.Reformulated.B.DYhc4.main :
    ∀ {K A : Type} [inst : Field K] [inst_1 : CommRing A] [inst_2 : Algebra K A] [Algebra.FiniteType K A] (σ : K →+* ℂ)
      (p : Ideal A) [hp : p.IsPrime] {b : A},
      b ∉ p →
        ∃ (ψ : A →+* ℂ), ψ.comp (Algebra.algebraMap K A) = σ ∧ (∀ a ∈ p, (ψ : A → ℂ) a = (0 : ℂ)) ∧ (ψ : A → ℂ) b ≠ (0 : ℂ) := by
  intro K A _ _ _ _ σ p hp b hb
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  have hj : p.jacobson = p := IsJacobsonRing.out' p hp.isRadical
  have hex : ∃ m : Ideal A, p ≤ m ∧ m.IsMaximal ∧ b ∉ m := by
    by_contra h
    push_neg at h
    apply hb
    rw [← hj]
    refine Ideal.mem_sInf.2 ?_
    rintro J ⟨hpJ, hJ⟩
    exact h J hpJ hJ
  obtain ⟨m, hpm, hm, hbm⟩ := hex
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  letI : Algebra K ℂ := σ.toAlgebra
  let f : (A ⧸ m) →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨(f : (A ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m), ?_, ?_, ?_⟩
  · ext x
    have h1 : Ideal.Quotient.mk m (algebraMap K A x) = algebraMap K (A ⧸ m) x := rfl
    have h2 : f (algebraMap K (A ⧸ m) x) = algebraMap K ℂ x := f.commutes x
    exact h2
  · intro a ha
    have : Ideal.Quotient.mk m a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hpm ha)
    simp [this]
  · intro h0
    have h1 : f (Ideal.Quotient.mk m b) = 0 := h0
    have h2 : Ideal.Quotient.mk m b = 0 := by
      simpa using (map_eq_zero f).1 h1
    exact hbm (Ideal.Quotient.eq_zero_iff_mem.1 h2)
