import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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

open CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

private theorem isReduced_stalk_of_isAffineOpen {Z : AlgebraicGeometry.Scheme} {V : Z.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V)
    (hred : _root_.IsReduced ↥(Z.presheaf.obj (Opposite.op V))) (x : V) :
    _root_.IsReduced ↥(Z.presheaf.stalk x.1) := by
  have := hV.isLocalization_stalk x
  exact isReduced_localizationPreserves (hV.primeIdealOf x).asIdeal.primeCompl
    ↥(Z.presheaf.stalk x.1) hred

private theorem isReduced_presheaf_obj_subscheme_ker {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X)
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] (U : X.affineOpens) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.obj
      (Opposite.op ((TopologicalSpace.Opens.map
        (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U.1))) := by
  have hid : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U
      = RingHom.ker (AlgebraicGeometry.Scheme.Hom.app f U.1).hom := by
    simp
  have hq : _root_.IsReduced (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U) := by
    rw [hid]
    exact isReduced_of_injective (RingHom.kerLift (AlgebraicGeometry.Scheme.Hom.app f U.1).hom)
      (RingHom.kerLift_injective _)
  have hq' : _root_.IsReduced ↥(CommRingCat.of (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U)) := hq
  exact isReduced_of_injective
    ((AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).hom.hom)
    (AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).commRingCatIsoToRingEquiv.injective

private theorem isReduced_stalk_subscheme_ker {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X)
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f]
    (y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU, hyU⟩ : ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base y ∈ U :=
    ⟨(X.affineCover.f (X.affineCover.idx _)).opensRange,
      AlgebraicGeometry.isAffineOpen_opensRange _, X.affineCover.covers _⟩
  have hVaff : AlgebraicGeometry.IsAffineOpen ((TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U) :=
    hU.preimage (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι
  have hyV : y ∈ (TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U := hyU
  have hred := isReduced_presheaf_obj_subscheme_ker f ⟨U, hU⟩
  exact isReduced_stalk_of_isAffineOpen hVaff hred ⟨y, hyV⟩

theorem isReduced_subscheme_ker {W X : AlgebraicGeometry.Scheme}
    (f : W ⟶ X) [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Scheme.Hom.ker f).subscheme := by
  have : ∀ y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme,
      _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) :=
    fun y => isReduced_stalk_subscheme_ker f y
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

end FunctorialResolution.EmbeddedResolution
