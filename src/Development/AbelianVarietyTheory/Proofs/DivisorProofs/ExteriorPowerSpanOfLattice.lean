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
import Mathlib.LinearAlgebra.ExteriorPower.Basic
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
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

theorem GlobalTheory.span_ιMulti_span_range_eq : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h N : ℕ) (g : Fin h → V), Submodule.span O {w : ⋀[C]^N V | ∃ x : Fin N → V, (∀ i, x i ∈ (Submodule.span O (Set.range g) : Set V)) ∧ w = exteriorPower.ιMulti C N x} = Submodule.span O (Set.range (fun s : Fin N → Fin h => exteriorPower.ιMulti C N (g ∘ s))) := by
  intro C _ O _ _ V _ _ _ _ h N g
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro w ⟨x, hx, rfl⟩
    have hc : ∀ i, ∃ c : Fin h → O, ∑ j, c j • g j = x i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun O).1 (hx i)
    choose c hc using hc
    have hx' : x = fun i => ∑ j, (algebraMap O C (c i j)) • g j := by
      funext i; rw [← hc i]; simp [algebraMap_smul]
    rw [hx']
    show (exteriorPower.ιMulti C N).toMultilinearMap (fun i => ∑ j, (algebraMap O C (c i j)) • g j) ∈ _
    rw [MultilinearMap.map_sum]
    refine Submodule.sum_mem _ (fun s _ => ?_)
    rw [MultilinearMap.map_smul_univ, ← map_prod, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · apply Submodule.span_mono
    rintro w ⟨s, rfl⟩
    exact ⟨g ∘ s, fun i => Submodule.subset_span ⟨s i, rfl⟩, rfl⟩
