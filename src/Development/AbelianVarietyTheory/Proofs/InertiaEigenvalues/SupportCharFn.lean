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
import Mathlib.RepresentationTheory.Basic
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

noncomputable section

open GlobalTheory.PRep
open scoped Classical

namespace GlobalTheory.KTypeTest

variable {G : Type} [Group G] (K : Subgroup G) {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]

def charFn (σ : Representation ℂ K U) (g : G) : ℂ :=
  if hg : g ∈ K then starRingEnd ℂ (LinearMap.trace ℂ U (σ ⟨g, hg⟩)) else 0

def IsKMap (σ : Representation ℂ K U) (ρ : Representation ℂ G V) (f : U →ₗ[ℂ] V) : Prop :=
  ∀ κ : K, f ∘ₗ σ κ = ρ κ ∘ₗ f

theorem support_charFn (σ : Representation ℂ K U) : Function.support (charFn K σ) ⊆ (K : Set G) := by
  intro g hg
  by_contra h
  exact hg (by simp [charFn, show g ∉ K from h])

theorem isKMap_zero (σ : Representation ℂ K U) (ρ : Representation ℂ G V) : IsKMap K σ ρ 0 := fun _ => by simp

end GlobalTheory.KTypeTest
