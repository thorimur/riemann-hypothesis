import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
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
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem preimage_eq_of_finite_appLE : ∀ {X Y : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ X) [IsSeparated π] {U : X.Opens} {V : Y.Opens}, IsAffineOpen U → IsAffineOpen V → (V : Set Y).Nonempty → ∀ h : V ≤ π ⁻¹ᵁ U, (π.appLE U V h).hom.Finite → π ⁻¹ᵁ U = V := by
  intro X Y _ π _ U V hU hV hne h hfin
  have : IsAffine U := hU
  have : IsAffine V := hV
  have hf : IsFinite (π.resLE U V h) := by
    have hS : IsFinite (Spec.map (π.resLE U V h).appTop) := (IsFinite.SpecMap_iff _).mpr
      ((RingHom.finite_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso π U V h)).mpr hfin)
    rw [Arrow.iso_w' (arrowIsoSpecΓOfIsAffine (π.resLE U V h)).symm]
    infer_instance
  have : UniversallyClosed (Y.homOfLE h ≫ π ∣_ U) := by
    change UniversallyClosed (π.resLE U V h)
    infer_instance
  have : UniversallyClosed (Y.homOfLE h) := .of_comp_of_isSeparated _ (π ∣_ U)
  obtain ⟨y, hy⟩ := hne
  have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨y, h hy⟩⟩
  have hcl : IsClopen (Set.range (Y.homOfLE h).base) :=
    ⟨(Y.homOfLE h).isClosedMap.isClosed_range,
      (Y.homOfLE h).isOpenEmbedding.isOpenMap.isOpen_range⟩
  have huniv : Set.range (Y.homOfLE h).base = Set.univ :=
    (isClopen_iff.mp hcl).resolve_left
      (Set.nonempty_iff_ne_empty.mp ⟨_, ⟨⟨y, hy⟩, rfl⟩⟩)
  refine le_antisymm (fun x hx => ?_) h
  obtain ⟨⟨w, hw⟩, hz⟩ : (⟨x, hx⟩ : π ⁻¹ᵁ U) ∈ Set.range (Y.homOfLE h).base := by
    rw [huniv]; trivial
  have hz' : ((Y.homOfLE h) ⟨w, hw⟩).1 = x := congrArg Subtype.val hz
  have hzx : w = x := (Scheme.homOfLE_apply h ⟨w, hw⟩).symm.trans hz'
  exact hzx ▸ hw

end GlobalTheory
