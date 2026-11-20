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
import Mathlib.RepresentationTheory.Coinduced
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
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

def funDiagRepresentation (X : Type*) [MulAction G X] (ρ : Representation k G V) :
    Representation k G (X → V) where
  toFun g :=
    { toFun := fun F x => ρ g (F (g⁻¹ • x))
      map_add' := fun F F' => funext fun x => map_add (ρ g) _ _
      map_smul' := fun c F => funext fun x => map_smul (ρ g) c _ }
  map_one' := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun F => funext fun x => ?_
    simp [mul_smul]

@[simp]
theorem funDiagRepresentation_apply (X : Type*) [MulAction G X] (ρ : Representation k G V) (g : G)
    (F : X → V) (x : X) : funDiagRepresentation X ρ g F x = ρ g (F (g⁻¹ • x)) :=
  rfl

abbrev funDiagRep {k G : Type u} [CommRing k] [Group G] (X : Type u) [MulAction G X]
    (A : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (funDiagRepresentation X A.ρ)

end GroundTheory.ProfCoh
