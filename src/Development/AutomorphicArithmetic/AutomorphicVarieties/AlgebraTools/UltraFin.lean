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

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ultra_fin :
    ∀ (ι Z : Type) (U : Ultrafilter ι) (a : ι → Z) (s : Set Z), s.Finite → (∀ᶠ i in (U : Filter ι), a i ∈ s) →
      ∃! z, z ∈ s ∧ ∀ᶠ i in (U : Filter ι), a i = z := by
  intro ι Z U a s hs h
  have hsub : {i | a i ∈ s} ⊆ ⋃ z ∈ s, {i | a i = z} := by
    intro i hi
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨a i, hi, rfl⟩
  have hmem : (⋃ z ∈ s, {i | a i = z}) ∈ U := U.1.sets_of_superset h hsub
  obtain ⟨z, hz, hzU⟩ := (Ultrafilter.finite_biUnion_mem_iff hs).1 hmem
  refine ⟨z, ⟨hz, hzU⟩, ?_⟩
  rintro w ⟨-, hw⟩
  obtain ⟨i, hi1, hi2⟩ := (hw.and hzU).exists
  exact hi1.symm.trans hi2
