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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory.DetAdResultant
theorem det_aeval_eq_resultant_of_splits {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (g : K[X]) (hg : g.Monic) (hs : g.Splits) :
    (aeval A g).det = resultant A.charpoly g := by
  rw [resultant_comm, resultant_eq_prod_eval g A.charpoly _ le_rfl hs, hg.leadingCoeff, one_pow, one_mul]
  let φ : K[X] →* K := Matrix.detMonoidHom.comp (aeval A).toMonoidHom
  have hφ : ∀ p, φ p = (aeval A p).det := fun p => rfl
  have h1 : ∀ x : K, φ (X - C x) = (-1) ^ Fintype.card ι * eval x A.charpoly := by
    intro x
    rw [hφ]
    simp only [map_sub, aeval_X, aeval_C, Matrix.eval_charpoly]
    rw [← Matrix.det_neg, neg_sub]
    rfl
  rw [← hφ]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hg]
  rw [map_multiset_prod, Multiset.map_map]
  simp only [Function.comp_def, h1]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← pow_mul,
    Matrix.charpoly_natDegree_eq_dim, ← hs.natDegree_eq_card_roots]

theorem det_aeval_eq_resultant {E : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι E) (g : E[X]) (hg : g.Monic) :
    (aeval A g).det = resultant A.charpoly g := by
  let K := AlgebraicClosure E
  apply (algebraMap E K).injective
  have h := det_aeval_eq_resultant_of_splits (A.map (algebraMap E K)) (g.map (algebraMap E K))
    (hg.map _) (IsAlgClosed.splits _)
  rw [Matrix.charpoly_map, natDegree_map, natDegree_map, resultant_map_map] at h
  rw [← h, RingHom.map_det]
  congr 1
  have e : (algebraMap E K).mapMatrix (aeval A g) = (Algebra.ofId E K).mapMatrix (aeval A g) := rfl
  rw [e, ← aeval_algHom_apply, aeval_map_algebraMap]
  rfl
theorem det_det_charmatrix {E : Type} [Field E] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (A : Matrix ι₁ ι₁ E) (B : Matrix ι₂ ι₂ E) :
    ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix B.transpose).map (aeval A).toRingHom)).det =
      resultant A.charpoly B.charpoly := by
  rw [← Matrix.det_det, ← Matrix.charpoly, Matrix.charpoly_transpose]
  exact det_aeval_eq_resultant A B.charpoly (Matrix.charpoly_monic B)

theorem toMatrix_ad {E : Type} [Field E] {V₁ V₂ : Type} [AddCommGroup V₁] [Module E V₁]
    [AddCommGroup V₂] [Module E V₂] {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂] (b₁ : Module.Basis ι₁ E V₁) (b₂ : Module.Basis ι₂ E V₂)
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂) :
    LinearMap.toMatrix (b₂.linearMap b₁) (b₂.linearMap b₁)
        (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      Matrix.reindex (Equiv.prodComm ι₂ ι₁) (Equiv.prodComm ι₂ ι₁)
        ((Matrix.comp ι₂ ι₂ ι₁ ι₁ E) ((Matrix.charmatrix (LinearMap.toMatrix b₂ b₂ f₂).transpose).map
          (aeval (LinearMap.toMatrix b₁ b₁ f₁)).toRingHom)) := by
  ext ⟨a, j⟩ ⟨b, k⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.linearMap_repr_apply]
  have hr : ∀ M : Matrix ι₁ ι₂ E, (Matrix.stdBasis E ι₁ ι₂).repr M (a, j) = M a j := fun M => rfl
  have hψ : LinearMap.toMatrix b₂ b₁ (b₂.linearMap b₁ (b, k)) = Matrix.single b k 1 := by
    simp [Module.Basis.linearMap, Matrix.stdBasis_eq_single]
  rw [hr, LinearMap.sub_apply, LinearMap.llcomp_apply', LinearMap.lcomp_apply', map_sub,
    LinearMap.toMatrix_comp b₂ b₁ b₁, LinearMap.toMatrix_comp b₂ b₂ b₁, hψ]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Matrix.comp_apply, Matrix.map_apply, Matrix.charmatrix_apply, Matrix.transpose_apply]
  by_cases hjk : j = k
  · subst hjk
    simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  · simp [Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.algebraMap_matrix_apply, hjk, Matrix.diagonal_apply_ne _ hjk]
    by_cases hab : a = b
    · subst hab; simp [Ne.symm hjk]
    · simp [hab, Ne.symm hab, Ne.symm hjk]

theorem det_ad_eq_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁]
    [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂]
    (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂),
    LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) =
      resultant f₁.charpoly f₂.charpoly := by
  intro E _ V₁ V₂ _ _ _ _ _ _ f₁ f₂
  let b₁ := Module.finBasis E V₁
  let b₂ := Module.finBasis E V₂
  rw [← LinearMap.det_toMatrix (b₂.linearMap b₁), toMatrix_ad b₁ b₂, Matrix.det_reindex_self,
    det_det_charmatrix, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix]

end GlobalTheory.DetAdResultant
