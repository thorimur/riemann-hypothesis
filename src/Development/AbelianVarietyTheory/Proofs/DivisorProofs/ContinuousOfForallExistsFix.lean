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

universe u_1 u_2 u_3 u_4

namespace GlobalTheory.ContinuityFromFixedPoints

open Topology

theorem continuous_of_forall_exists_fix {k : Type u_1} {F : Type u_2} {k' : Type u_3}
    {F' : Type u_4} [Field k] [Field F] [Algebra k F] [Field k'] [Field F'] [Algebra k' F']
    [Algebra.IsIntegral k F] (φ : Gal(F/k) →* Gal(F'/k'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : Gal(F/k), σ x = x → φ σ y = y) :
    Continuous φ := by
  classical
  choose x hx using h
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E', hE', hs'⟩ := (krullTopology_mem_nhds_one_iff k' F' s).1 hs
  let b := Module.finBasis k' E'
  let S : Set F := Set.range fun i => x (b i : F')
  have hS : S.Finite := Set.finite_range _
  haveI : Finite S := hS.to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff k F _).2 ⟨IntermediateField.adjoin k S, hfin, ?_⟩
  intro σ hσ
  apply hs'
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, φ σ (b i : F') = b i := fun i =>
    hx _ σ (hσ _ (IntermediateField.subset_adjoin k S ⟨i, rfl⟩))
  intro y hy
  have hlin : ((φ σ).toLinearMap ∘ₗ E'.val.toLinearMap) = E'.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun hlin ⟨y, hy⟩

end GlobalTheory.ContinuityFromFixedPoints
