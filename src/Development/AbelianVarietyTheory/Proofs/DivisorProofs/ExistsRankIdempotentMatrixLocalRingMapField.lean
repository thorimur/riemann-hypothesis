import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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

open Matrix

namespace GlobalTheory.IdemRankLocal

theorem exists_conj_diag (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ)
    (p : Matrix (Fin n) (Fin n) W) (hp : p * p = p) :
    ∃ (r : ℕ) (P P' : Matrix (Fin n) (Fin n) W), P * P' = 1 ∧
    p = P * Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) * P' := by
  classical
  set f : (Fin n → W) →ₗ[W] (Fin n → W) := Matrix.toLin' p with hfdef
  have hf : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, hfdef, ← Matrix.toLin'_mul, hp]
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  haveI : Module.Projective W (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc x)
  haveI : Module.Projective W (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm x)
  haveI : Module.Finite W (LinearMap.range f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Finite W (LinearMap.ker f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (Submodule.linearProjOfIsCompl_surjective hc.symm)
  haveI : Module.Free W (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free W (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  set r := Module.finrank W (LinearMap.range f)
  set s := Module.finrank W (LinearMap.ker f)
  let b1 := Module.finBasis W (LinearMap.range f)
  let b2 := Module.finBasis W (LinearMap.ker f)
  let bs : Module.Basis (Fin r ⊕ Fin s) W (Fin n → W) :=
    (b1.prod b2).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hrs : r + s = n := by
    have := Module.finrank_eq_card_basis bs
    simpa [Fintype.card_sum] using this.symm
  have hbs1 : ∀ i, f (bs (Sum.inl i)) = bs (Sum.inl i) := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
    obtain ⟨y, hy⟩ := (b1 i).2
    rw [← hy]
    exact LinearMap.congr_fun hf y
  have hbs2 : ∀ i, f (bs (Sum.inr i)) = 0 := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
  let b : Module.Basis (Fin n) W (Fin n → W) := bs.reindex (finSumFinEquiv.trans (finCongr hrs))
  have hb : ∀ j : Fin n, f (b j) = (if j.val < r then (1 : W) else 0) • b j := by
    intro j
    have hj : b j = bs ((finSumFinEquiv.trans (finCongr hrs)).symm j) := Module.Basis.reindex_apply _ _ _
    rw [hj]
    by_cases h : j.val < r
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inl ⟨j, h⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp
      rw [this, if_pos h, one_smul, hbs1]
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inr ⟨j.val - r, by omega⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp; omega
      rw [this, if_neg h, zero_smul, hbs2]
  have hdiag : LinearMap.toMatrix b b f = Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, b.repr_self]
    by_cases hij : i = j
    · subst hij; simp; split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, Finsupp.single_apply, Ne.symm hij]
      split_ifs <;> simp [Finsupp.single_apply, Ne.symm hij]
  let e := Pi.basisFun W (Fin n)
  refine ⟨r, e.toMatrix b, b.toMatrix e, ?_, ?_⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip e b
  · have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f
    rw [← hdiag, this, LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']

theorem rank_map_const : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W),
    Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  intro W _ _ n Q hQ
  classical
  obtain ⟨r, P, P', hPP', hQeq⟩ := exists_conj_diag W n Q hQ
  refine ⟨Fintype.card {i : Fin n // i.val < r}, fun k _ β => ?_⟩
  have hm : P.map β * P'.map β = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ β.map_zero β.map_one]
  have hP : IsUnit (P.map β).det := Matrix.isUnit_det_of_right_inverse hm
  have hP' : IsUnit (P'.map β).det := Matrix.isUnit_det_of_left_inverse hm
  rw [hQeq, Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP, Matrix.diagonal_map β.map_zero,
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by split_ifs with h <;> simp [h]))

end GlobalTheory.IdemRankLocal
