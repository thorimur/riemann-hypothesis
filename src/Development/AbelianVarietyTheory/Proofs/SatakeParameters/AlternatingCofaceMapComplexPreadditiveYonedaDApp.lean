import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
open CategoryTheory Limits AlgebraicGeometry Opposite Abelian Simplicial GlobalTheory.Et
universe v u

namespace GlobalTheory

theorem alternatingCofaceMapComplex_preadditiveYoneda_d_apply {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C) (I : C) (m : ℕ)
  (x : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).X m) :
  ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1) x
   = (show X _⦋m+1⦌ ⟶ I from AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) := by
  have hd : ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d m (m+1)
      = AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I) m := by
    exact CochainComplex.of_d (fun n => (X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋n⦌)
      (AlgebraicTopology.AlternatingCofaceMapComplex.objD (X.rightOp ⋙ preadditiveYoneda.obj I)) m
  rw [hd]
  let φ : (((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m⦌) ⟶ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌)) →+ ((X.rightOp ⋙ preadditiveYoneda.obj I).obj ⦋m+1⦌) :=
    AddMonoidHom.mk' (fun f => f x) (fun f g => rfl)
  change φ (AlgebraicTopology.AlternatingCofaceMapComplex.objD _ m) = _
  have h2 : (AlgebraicTopology.AlternatingFaceMapComplex.objD X m ≫ (show X _⦋m⦌ ⟶ I from x)) =
      ∑ i : Fin (m+2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i ≫ (show X _⦋m⦌ ⟶ I from x)) := by
    rw [AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun i _ => Preadditive.zsmul_comp _ _ _
  refine Eq.trans ?_ h2.symm
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, map_sum, map_zsmul]
  rfl

theorem alternatingCofaceMapComplex_preadditiveYoneda_exactAt_succ : ∀ {C : Type u} [Category.{v} C] [Abelian C] (X : SimplicialObject C) (I : C) [Injective I] (n : ℕ), ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).ExactAt (n + 1) → ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).ExactAt (n + 1) := by
  intro C _ _ X I _ n h
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff' _ n (n+1) (n+2) (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro x hx
  let S := ((AlgebraicTopology.alternatingFaceMapComplex C).obj X).sc' (n+2) (n+1) n
  have hS1 : S.f = AlgebraicTopology.AlternatingFaceMapComplex.objD X (n+1) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X (n+1)
  have hS2 : S.g = AlgebraicTopology.AlternatingFaceMapComplex.objD X n :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq X n
  let f : S.X₂ ⟶ I := x
  have hf : S.f ≫ f = 0 := by
    have h1 := alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I (n+1) x
    rw [hS1]
    exact h1.symm.trans hx
  have hm : Mono (cokernel.desc S.f S.g S.zero) := h.mono_cokernelDesc
  let g : S.X₃ ⟶ I := @Injective.factorThru _ _ _ _ _ _ (cokernel.desc S.f f hf) (cokernel.desc S.f S.g S.zero) hm
  refine ⟨g, ?_⟩
  change ((AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{v}).obj (X.rightOp ⋙ preadditiveYoneda.obj I)).d n (n+1) g = x
  refine (alternatingCofaceMapComplex_preadditiveYoneda_d_apply X I n g).trans ?_
  rw [← hS2]
  change S.g ≫ g = f
  have e2 : cokernel.desc S.f S.g S.zero ≫ g = cokernel.desc S.f f hf :=
    @Injective.comp_factorThru _ _ _ _ _ _ _ _ hm
  rw [← cokernel.π_desc S.f S.g S.zero, Category.assoc, e2, cokernel.π_desc]

end GlobalTheory
