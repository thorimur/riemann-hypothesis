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

namespace GlobalTheory

theorem clopen_image_irreducibleComponent : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by
  intro A B _ _ f hf hop hcl hcomp S hS hSc a ha
  refine ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a,
    mem_irreducibleComponent, ?_⟩
  have hCc : IsClosed (irreducibleComponent a) := isClosed_irreducibleComponent
  have hCo : IsOpen (irreducibleComponent a) :=
    hcomp _ (irreducibleComponent_mem_irreducibleComponents a)
  have hCp : IsPreconnected (irreducibleComponent a) :=
    (IsIrreducible.isConnected (isIrreducible_irreducibleComponent (x := a))).isPreconnected
  have hsub : irreducibleComponent a ⊆ f ⁻¹' S :=
    hCp.subset_isClopen (hS.preimage hf) ⟨a, mem_irreducibleComponent, ha⟩
  have himg : f '' irreducibleComponent a ⊆ S := Set.image_subset_iff.mpr hsub
  have hclo : IsClopen (f '' irreducibleComponent a) := ⟨hcl _ hCc, hop _ hCo⟩
  refine le_antisymm himg ?_
  exact hSc.subset_isClopen hclo ⟨f a, ha, a, mem_irreducibleComponent, rfl⟩

end GlobalTheory
