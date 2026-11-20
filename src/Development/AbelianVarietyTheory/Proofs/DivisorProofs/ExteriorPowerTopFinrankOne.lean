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
import Mathlib.LinearAlgebra.ExteriorPower.Basis
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
import Mathlib.Topology.Sheaves.Init
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem topWedge_line_and_nonzero : ∀ (C : Type) [Field C] (V : Type) [AddCommGroup V] [Module C V] (h N : ℕ) (g : Fin h → V), Submodule.span C (Set.range g) = ⊤ → Module.finrank C V = N → Module.finrank C (⋀[C]^N V) = 1 ∧ ∃ s : Fin N → Fin h, exteriorPower.ιMulti C N (g ∘ s) ≠ 0 := by
  intro C _ V _ _ h N g hspan hN
  haveI : Module.Finite C V := ⟨by rw [← hspan]; exact Submodule.fg_span (Set.finite_range g)⟩
  have h1 : Module.finrank C (⋀[C]^N V) = 1 := by
    rw [exteriorPower.finrank_eq, hN, Nat.choose_self]
  refine ⟨h1, ?_⟩
  by_contra hcon
  push_neg at hcon
  have htop := exteriorPower.ιMulti_span_of_span C N V hspan
  have hle : Submodule.span C (exteriorPower.ιMulti C N '' {a | Set.range a ⊆ Set.range g}) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro - ⟨a, ha, rfl⟩
    have hmem : ∀ i, ∃ j, g j = a i := fun i => ha ⟨i, rfl⟩
    choose s hs using hmem
    have : a = g ∘ s := funext fun i => (hs i).symm
    rw [this, hcon s]
    simp
  rw [htop, le_bot_iff] at hle
  have : Subsingleton (⋀[C]^N V) := subsingleton_of_forall_eq 0 fun x => by
    have hx : x ∈ (⊤ : Submodule C (⋀[C]^N V)) := trivial
    rw [hle] at hx
    simpa using hx
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact absurd h1 (by norm_num)

end GlobalTheory
