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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Semisimple
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
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range :
    ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  intro G _ W _ _ ρ J V _ _ r p hr hp htop
  let f : ∀ j, (r j).IntertwiningMap ρ := fun j => ⟨p j, fun g => LinearMap.ext fun v => hp j g v⟩
  let F : ∀ j, (r j).asModule →ₗ[MonoidAlgebra ℂ G] ρ.asModule :=
    fun j => Representation.IntertwiningMap.equivLinearMapAsModule (r j) ρ (f j)
  have hF : ∀ j (v : V j), F j v = p j v := fun j v => rfl
  have hs : ∀ j, IsSemisimpleModule (MonoidAlgebra ℂ G) (LinearMap.range (F j)) := by
    intro j
    haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (r j)).mp
      (hr j)
    exact IsSemisimpleModule.range (F j)
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' hs ?_
  rw [eq_top_iff]
  intro x _
  have hx : (show W from x) ∈ ⨆ j, LinearMap.range (p j) := by
    rw [htop]
    exact Submodule.mem_top
  refine Submodule.iSup_induction (fun j => LinearMap.range (p j))
    (motive := fun y : W => (show ρ.asModule from y) ∈ ⨆ j, LinearMap.range (F j)) hx ?_ ?_ ?_
  · rintro j y ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem j ⟨v, hF j v⟩
  · exact Submodule.zero_mem _
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

end GlobalTheory.ClassFin
