import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.TensorAlgebra.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem trdeg_le_of_ringEquiv_square {K L K' L' : Type} [Field K] [Field L] [Field K'] [Field L']
    (f : K →+* L) (f' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : f'.comp (eK : K →+* K') = (eL : L →+* L').comp f) :
    @Algebra.trdeg K L _ _ f.toAlgebra ≤ @Algebra.trdeg K' L' _ _ f'.toAlgebra := by
  letI := f.toAlgebra
  letI := f'.toAlgebra
  haveI : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr f.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K L
  rw [← hs.cardinalMk_eq_trdeg]
  have hi : AlgebraicIndependent K' ((eL : L → L') ∘ ((↑) : s → L)) :=
    (algebraicIndependent_ringHom_iff_of_comp_eq eK (eL : L →+* L') eL.injective h).mpr hs.1
  simpa using hi.lift_cardinalMk_le_trdeg

theorem trdeg_eq_of_ringEquiv_square {K L K' L' : Type} [Field K] [Field L] [Field K'] [Field L']
    (f : K →+* L) (f' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : f'.comp (eK : K →+* K') = (eL : L →+* L').comp f) :
    @Algebra.trdeg K L _ _ f.toAlgebra = @Algebra.trdeg K' L' _ _ f'.toAlgebra := by
  refine le_antisymm (trdeg_le_of_ringEquiv_square f f' eK eL h)
    (trdeg_le_of_ringEquiv_square f' f eK.symm eL.symm ?_)
  ext x
  have := congrArg (fun g => eL.symm (g (eK.symm x))) h
  simpa using this.symm

end GlobalTheory

namespace GlobalTheory
theorem ΓSpecIso_inv_germ_residue_residueFieldMap {R B : CommRingCat.{0}} (φ : R ⟶ B) (x : Spec B) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ (Spec.map φ x) trivial ≫
        (Spec R).residue (Spec.map φ x) ≫ (Spec.map φ).residueFieldMap x =
      φ ≫ (Scheme.ΓSpecIso B).inv ≫ (Spec B).presheaf.germ ⊤ x trivial ≫ (Spec B).residue x := by
  rw [Scheme.residue_residueFieldMap]
  erw [Scheme.Hom.germ_stalkMap_assoc (Spec.map φ) ⊤ x trivial]
  have hn := Scheme.ΓSpecIso_naturality φ
  rw [← Category.assoc, ← Category.assoc φ]
  congr 1
  show (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop = φ ≫ (Scheme.ΓSpecIso B).inv
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
end GlobalTheory

namespace GlobalTheory

end GlobalTheory

namespace GlobalTheory

end GlobalTheory
