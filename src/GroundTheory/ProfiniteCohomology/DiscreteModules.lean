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

namespace GroundTheory.ProfCoh

open CategoryTheory

universe w u v

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

def stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]

@[simp]
theorem mem_stabilizer {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (v : V) (g : G) : g ∈ stabilizer ρ v ↔ ρ g v = v :=
  Iff.rfl

variable [TopologicalSpace G]

class IsDiscreteRep (A : Rep.{w} k G) : Prop where
  isOpen_stabilizer : ∀ a : A, IsOpen (stabilizer A.ρ a : Set G)

theorem isOpen_stabilizer (A : Rep.{w} k G) [IsDiscreteRep A] (a : A) :
    IsOpen (stabilizer A.ρ a : Set G) :=
  IsDiscreteRep.isOpen_stabilizer a

theorem isDiscreteRep_iff (A : Rep.{w} k G) :
    IsDiscreteRep A ↔ ∀ a : A, IsOpen (stabilizer A.ρ a : Set G) :=
  ⟨fun h => h.isOpen_stabilizer, fun h => ⟨h⟩⟩

variable (k G) in

def isDiscreteRep : ObjectProperty (Rep.{w} k G) := fun A => IsDiscreteRep A

@[simp]
theorem isDiscreteRep_apply (A : Rep.{w} k G) : isDiscreteRep k G A ↔ IsDiscreteRep A :=
  Iff.rfl

variable (k G) in

abbrev DiscreteRep := (isDiscreteRep.{w} k G).FullSubcategory

instance (A : DiscreteRep.{w} k G) : IsDiscreteRep A.obj := A.property

end GroundTheory.ProfCoh
