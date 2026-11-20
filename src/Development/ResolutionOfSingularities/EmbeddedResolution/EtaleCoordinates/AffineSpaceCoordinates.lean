import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIndexedBy (k : Type u) [Field k] (n : Type u) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace n (Spec (CommRingCat.of k))

abbrev affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : Type u) :
    affineSpaceIndexedBy k n ⟶ Spec (CommRingCat.of k) :=
  affineSpaceIndexedBy k n ↘ Spec (CommRingCat.of k)

def pullbackCoord {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) : Γ(Y, ⊤) :=
  f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i)

@[simp]
theorem pullbackCoord_def {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord f i = f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) := rfl

def coordVectorInl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun a => pullbackCoord f (ULift.up a)) (fun _ => 0) i.down

@[simp]
theorem coordVectorInl_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (a : Fin n) :
    coordVectorInl n m f (ULift.up (Sum.inl a)) = pullbackCoord f (ULift.up a) := rfl

@[simp]
theorem coordVectorInl_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (b : Fin m) :
    coordVectorInl n m f (ULift.up (Sum.inr b)) = 0 := rfl

def coordVectorInr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun _ => 0) (fun b => pullbackCoord f (ULift.up b)) i.down

@[simp]
theorem coordVectorInr_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (a : Fin n) :
    coordVectorInr n m f (ULift.up (Sum.inl a)) = 0 := rfl

@[simp]
theorem coordVectorInr_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (b : Fin m) :
    coordVectorInr n m f (ULift.up (Sum.inr b)) = pullbackCoord f (ULift.up b) := rfl

end FunctorialResolution.EmbeddedResolution
