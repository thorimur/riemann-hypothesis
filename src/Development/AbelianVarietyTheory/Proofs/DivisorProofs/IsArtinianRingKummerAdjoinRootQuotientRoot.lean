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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open IsLocalRing Polynomial

namespace GlobalTheory

theorem artinian_quot_root_adjoin_kummer (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (u : Aˣ) (m k : ℕ) (hϖ : Irreducible ϖ) (hm : IsUnit (m : A)) (hk : 0 < k) :
    IsArtinianRing (AdjoinRoot (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A))) ⧸ Ideal.span {AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)))}) := by
  set f : A[X] := X ^ m - C (u : A) with hf
  set R1 := AdjoinRoot f
  set g : R1[X] := X ^ k - C (AdjoinRoot.of f ϖ * AdjoinRoot.root f) with hg
  set R := AdjoinRoot g
  set I : Ideal R := Ideal.span {AdjoinRoot.root g}
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hfm : f.Monic := monic_X_pow_sub_C _ hm0
  have hgm : g.Monic := monic_X_pow_sub_C _ hk.ne'
  haveI : Module.Finite A R1 := (AdjoinRoot.powerBasis' hfm).finite
  haveI : Module.Finite R1 R := (AdjoinRoot.powerBasis' hgm).finite
  haveI : Module.Finite A R := Module.Finite.trans R1 R
  haveI : Module.Finite A (R ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap Ideal.Quotient.mk_surjective

  have hzero : algebraMap A (R ⧸ I) ϖ = 0 := by
    have h1 : (AdjoinRoot.root g) ^ k = AdjoinRoot.of g (AdjoinRoot.of f ϖ * AdjoinRoot.root f) := by
      have := AdjoinRoot.eval₂_root g
      rw [hg] at this
      simpa [eval₂_sub, sub_eq_zero] using this
    have h2 : (AdjoinRoot.root f) ^ m = AdjoinRoot.of f (u : A) := by
      have := AdjoinRoot.eval₂_root f
      rw [hf] at this
      simpa [eval₂_sub, sub_eq_zero] using this
    let q : R →+* R ⧸ I := Ideal.Quotient.mk I
    have ht : q (AdjoinRoot.root g) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have h3 : q (AdjoinRoot.of g (AdjoinRoot.of f ϖ)) * q (AdjoinRoot.of g (AdjoinRoot.root f)) = 0 := by
      rw [← map_mul, ← map_mul, ← h1, map_pow, ht, zero_pow hk.ne']
    have hu : IsUnit (q (AdjoinRoot.of g (AdjoinRoot.root f))) := by
      have : IsUnit (q (AdjoinRoot.of g (AdjoinRoot.root f)) ^ m) := by
        rw [← map_pow, ← map_pow, h2]
        exact (u.isUnit.map (AdjoinRoot.of f)).map _ |>.map _
      exact (isUnit_pow_iff hm0).mp this
    have h4 : q (AdjoinRoot.of g (AdjoinRoot.of f ϖ)) = 0 := by
      simpa [hu.mul_left_eq_zero] using h3
    exact h4
  have hmax : (Ideal.span {ϖ} : Ideal A).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  let K := A ⧸ (Ideal.span {ϖ} : Ideal A)
  letI : Field K := Ideal.Quotient.field _
  let φ : K →+* R ⧸ I := Ideal.Quotient.lift _ (algebraMap A (R ⧸ I)) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hzero])
  letI : Algebra K (R ⧸ I) := φ.toAlgebra
  haveI : IsScalarTower A K (R ⧸ I) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Module.Finite K (R ⧸ I) := Module.Finite.of_restrictScalars_finite A K (R ⧸ I)
  exact IsArtinianRing.of_finite K (R ⧸ I)

end GlobalTheory
