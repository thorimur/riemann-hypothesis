import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
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
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.FiniteTypeColimit

noncomputable def diagram (A : CommRingCat.{0}) : Finset A ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (Algebra.adjoin ℤ (t : Set A))
  map {s t} h := CommRingCat.ofHom
    (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 (leOfHom h)))).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def inclusions (A : CommRingCat.{0}) : diagram A ⟶ (Functor.const (Finset A)).obj A where
  app t := CommRingCat.ofHom (Algebra.adjoin ℤ (t : Set A)).val.toRingHom
  naturality _ _ _ := rfl

noncomputable def isColimit (A : CommRingCat.{0}) : IsColimit (Cocone.mk A (inclusions A)) := by
  classical
  haveI : ReflectsColimit (diagram A) (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y hxy => ?_)
  · exact ⟨{x}, ⟨x, Algebra.subset_adjoin (by simp)⟩, rfl⟩
  · have : x = y := Subtype.ext hxy
    exact ⟨i, 𝟙 i, by rw [this]⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.FiniteTypeColimit.finiteType (A : CommRingCat.{0}) (t : Finset A) :
    Algebra.FiniteType ℤ ((_root_.GlobalTheory.FiniteTypeColimit.diagram A).obj t) := by
  have h : (Algebra.adjoin ℤ (t : Set A)).FG := Subalgebra.fg_adjoin_finset t
  have := (Subalgebra.fg_iff_finiteType _).1 h
  change Algebra.FiniteType ℤ (CommRingCat.of (Algebra.adjoin ℤ (t : Set A)))
  convert this

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in

theorem _root_.GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType : ∀ A : CommRingCat.{0},
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
      (ι : D ⟶ (Functor.const J).obj A),
      Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) :=
  fun A => ⟨Finset A, inferInstance, inferInstance, _root_.GlobalTheory.FiniteTypeColimit.diagram A,
    _root_.GlobalTheory.FiniteTypeColimit.inclusions A, ⟨_root_.GlobalTheory.FiniteTypeColimit.isColimit A⟩,
    _root_.GlobalTheory.FiniteTypeColimit.finiteType A⟩

end GlobalTheory.FiniteTypeColimit
