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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init

namespace ReciprocityTheory.CA

open Polynomial RingTheory.Sequence

theorem pstep_monic_mem_of_mul {S : Type*} [CommRing S] (J : Ideal S) {g h : S[X]} (hg : g.Monic)
    (hgh : g * h ∈ J.map (C : S →+* S[X])) : h ∈ J.map (C : S →+* S[X]) := by

  have hk : RingHom.ker (mapRingHom (Ideal.Quotient.mk J)) = J.map (C : S →+* S[X]) := by
    rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
  rw [← hk, RingHom.mem_ker] at hgh ⊢
  simp only [map_mul, coe_mapRingHom] at hgh
  rw [coe_mapRingHom]
  exact ((hg.map (Ideal.Quotient.mk J)).mul_right_eq_zero_iff).mp hgh

theorem isWeaklyRegular_map_C_append_monic {S : Type*} [CommRing S] {rs : List S}
    (hrs : IsWeaklyRegular S rs) {g : S[X]} (hg : g.Monic) :
    IsWeaklyRegular S[X] (rs.map C ++ [g]) := by
  rw [isWeaklyRegular_append_iff]
  refine ⟨?_, ?_⟩
  · have h := hrs.of_flat (S := S[X])
    rwa [Polynomial.algebraMap_eq] at h
  · rw [isWeaklyRegular_singleton_iff]
    have hI : (Ideal.ofList (rs.map C) • ⊤ : Submodule S[X] S[X]) =
        (Ideal.ofList rs).map (C : S →+* S[X]) := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_ofList]
    intro a b hab
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    change g • Submodule.Quotient.mk a = g • Submodule.Quotient.mk b at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hI] at hab
    rw [smul_eq_mul, smul_eq_mul, ← mul_sub] at hab
    rw [Submodule.Quotient.eq, hI]
    exact pstep_monic_mem_of_mul _ hg hab

theorem isWeaklyRegular_map_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T)
    {rs : List S} (hrs : IsWeaklyRegular S rs) : IsWeaklyRegular T (rs.map e) := by
  letI : Algebra S T := e.toRingHom.toAlgebra

  let l : T ≃ₗ[S] S :=
    { e.symm.toAddEquiv with
      map_smul' := fun c t => by
        change e.symm (algebraMap S T c * t) = c * e.symm t
        rw [RingHom.algebraMap_toAlgebra, map_mul]
        simp }
  haveI : Module.Flat S T := Module.Flat.of_linearEquiv l
  exact hrs.of_flat

end ReciprocityTheory.CA
