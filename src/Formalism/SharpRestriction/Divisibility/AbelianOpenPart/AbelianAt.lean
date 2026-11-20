import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

namespace Formalism.MainNotions.DIV.Cons

universe u

attribute [local instance] CategoryTheory.Hom.group

abbrev GrpSch (S : Scheme.{u}) : Type (u + 1) := Grp (Over S)

def IsAbSch {S : Scheme.{u}} (A : GrpSch S) : Prop :=
  IsCommMonObj A.X ∧ IsProper A.X.hom ∧ Smooth A.X.hom ∧ GeometricallyConnected A.X.hom

def AbSch (S : Scheme.{u}) : Type (u + 1) := {A : GrpSch S // IsAbSch A}

def bchG {S T : Scheme.{u}} (f : T ⟶ S) (A : GrpSch S) : GrpSch T :=
  (Over.pullback f).mapGrp.obj A

def nMul {S : Scheme.{u}} (A : GrpSch S) (N : ℕ) : A.X ⟶ A.X := (𝟙 A.X) ^ N

def tors {S : Scheme.{u}} (A : GrpSch S) (N : ℕ) : Over S :=
  pullback (nMul A N) (MonObj.one : 𝟙_ (Over S) ⟶ A.X)

structure RAct (R : Type) [Ring R] {S : Scheme.{u}} (A : GrpSch S) where
  act : R → (A.X ⟶ A.X)
  hom : ∀ a, IsMonHom (act a)
  map_one : act 1 = 𝟙 A.X
  map_mul : ∀ a b, act (a * b) = act b ≫ act a
  map_add : ∀ a b, act (a + b) = act a * act b

def fibreAt {Z : Scheme.{u}} (A : GrpSch Z) (x : Z) : GrpSch (Spec (Z.residueField x)) :=
  bchG (Z.fromSpecResidueField x) A

def AbelianAt {Z : Scheme.{u}} (A : GrpSch Z) (x : Z) : Prop := IsAbSch (fibreAt A x)

structure ModelG (O : Type u) [CommRing O] [IsLocalRing O] where
  Z : Scheme.{u}
  str : Z ⟶ Spec (CommRingCat.of O)
  G : GrpSch Z

def ModelG.spf {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) : Scheme.{u} :=
  M.str.fiber (IsLocalRing.closedPoint O)

def ModelG.Gen {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) : Type u :=
  ↥(irreducibleComponents M.spf)

def ModelG.gpt {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) (η : M.Gen) : M.Z :=
  M.str.fiberι _ (η.2.1.genericPoint)

def ModelG.abAt {O : Type u} [CommRing O] [IsLocalRing O] (M : ModelG O) (η : M.Gen) : Prop :=
  AbelianAt M.G (M.gpt η)

end Formalism.MainNotions.DIV.Cons
