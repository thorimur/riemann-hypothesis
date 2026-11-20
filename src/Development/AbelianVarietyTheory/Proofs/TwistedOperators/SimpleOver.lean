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
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
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

open scoped TensorProduct

namespace GlobalTheory.TensHead

def Stab {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (N : Submodule ℂ V) : Prop :=
  ∀ g ∈ G, ∀ x ∈ N, g x ∈ N

def SimpleOver {V : Type} [AddCommGroup V] [Module ℂ V] (G : Set (Module.End ℂ V))
    (K : Submodule ℂ V) : Prop :=
  ∀ N : Submodule ℂ V, Stab G N → K ≤ N → N = K ∨ N = ⊤

def piOp {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i)) : Module.End ℂ (⨂[ℂ] j, M j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)

def piOps {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) :
    Set (Module.End ℂ (⨂[ℂ] j, M j)) :=
  {f | ∃ i, ∃ g ∈ Op i, f = piOp i g}

def tensOps {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (A : Set (Module.End ℂ V₀)) (B : Set (Module.End ℂ V₁)) : Set (Module.End ℂ (V₀ ⊗[ℂ] V₁)) :=
  {f | ∃ g ∈ A, f = TensorProduct.map g LinearMap.id} ∪
    {f | ∃ h ∈ B, f = TensorProduct.map LinearMap.id h}

def piKer {ι : Type} {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (K : ∀ i, Submodule ℂ (M i)) : Submodule ℂ (⨂[ℂ] j, M j) :=
  Submodule.span ℂ {t | ∃ y : ∀ i, M i, (∃ i, y i ∈ K i) ∧ t = PiTensorProduct.tprod ℂ y}

def tensKer {V₀ V₁ : Type} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (K₀ : Submodule ℂ V₀) (K₁ : Submodule ℂ V₁) : Submodule ℂ (V₀ ⊗[ℂ] V₁) :=
  Submodule.span ℂ {t | ∃ (x : V₀) (y : V₁), (x ∈ K₀ ∨ y ∈ K₁) ∧ t = x ⊗ₜ[ℂ] y}

end GlobalTheory.TensHead
