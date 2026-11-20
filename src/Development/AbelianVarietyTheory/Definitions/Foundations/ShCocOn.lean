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

noncomputable section

open scoped Matrix

namespace GlobalTheory.KA

variable {Γ : Type*} [Group Γ] {R : Type*} [CommRing R]

def ShCoc {X : Type*} [Monoid X] (ρ : Γ → Matrix (Fin 2) (Fin 2) R) (κ : Γ →* X) (Y : Γ → X → Fin 2 → R) : Prop :=
  ∀ s t x, Y (s * t) x = Y s x + ρ s *ᵥ Y t (x * κ s)

def ShCocOn {X : Type*} [Monoid X] (H : Subgroup Γ) (ν : Γ → R) (κ : Γ →* X) (z : Γ → X → R) : Prop :=
  ∀ s ∈ H, ∀ t ∈ H, ∀ x, z (s * t) x = z s x + ν s * z t (x * κ s)

def push {X X' : Type*} [Fintype X'] [DecidableEq X] {M : Type*} [AddCommMonoid M] (π : X' → X) (Y : Γ → X' → M) :
    Γ → X → M :=
  fun s x => ∑ x' ∈ Finset.univ.filter (fun x' => π x' = x), Y s x'

def spec {X : Type*} [Fintype X] (η : X → R) (Y : Γ → X → Fin 2 → R) : Γ → Fin 2 → R :=
  fun s => ∑ x, η x • Y s x

end GlobalTheory.KA

end
