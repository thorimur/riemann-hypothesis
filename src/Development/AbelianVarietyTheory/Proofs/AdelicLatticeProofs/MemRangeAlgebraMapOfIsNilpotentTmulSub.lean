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
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_algHom_algebraicClosure_ker_le (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    ∃ φ : A →ₐ[K] AlgebraicClosure K, ∀ x, φ x = 0 → x ∈ m := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let ι : (A ⧸ m) →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  refine ⟨ι.comp (Ideal.Quotient.mkₐ K m), fun x hx => ?_⟩
  have h : ι (Ideal.Quotient.mk m x) = 0 := hx
  have h2 : Ideal.Quotient.mk m x = 0 := ι.toRingHom.injective (by simpa using h)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem mem_range_algebraMap_of_isNilpotent_tmul_sub (K A : Type) [Field K] [CharZero K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsReduced A] (f : A)
    (hf : IsNilpotent (f ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] f)) : f ∈ (algebraMap K A).range := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have h1 : ∀ φ ψ : A →ₐ[K] AlgebraicClosure K, φ f = ψ f := by
    intro φ ψ
    have h := (hf.map (Algebra.TensorProduct.productMap φ ψ)).eq_zero
    simpa [sub_eq_zero] using h
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -⟩ := exists_algHom_algebraicClosure_ker_le K A m₀
  have h2 : φ₀ f ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    exact h1 (σ.toAlgHom.comp φ₀) φ₀
  obtain ⟨c, hc⟩ := h2
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  refine ⟨c, ?_⟩
  have h3 : f - algebraMap K A c ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ⟩ := exists_algHom_algebraicClosure_ker_le K A m
    apply hφ
    rw [map_sub, AlgHom.commutes, hc, h1 φ φ₀, sub_self]
  have h4 : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)
  rw [h4, Ideal.mem_bot, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.ClassFin
