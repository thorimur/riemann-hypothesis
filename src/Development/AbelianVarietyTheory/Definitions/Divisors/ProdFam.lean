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

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E : Type} [AddCommGroup E] [Module k E]

open Classical in

def idxSign (τ : κ → ι) (S : Finset κ) : ℤ := (-1) ^ ((S ×ˢ S).filter fun x => x.1 < x.2 ∧ τ x.2 < τ x.1).card

open Classical in

def pullIdx (τ : κ → ι) (a : Finset ι → E) : Finset κ → E := fun S =>
  if Set.InjOn τ (S : Set κ) then idxSign τ S • a (S.image τ) else 0

end Pull

section Cross

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

def fstL : ι ×ₗ κ → ι := fun x => (ofLex x).1

def sndL : ι ×ₗ κ → κ := fun x => (ofLex x).2

def crossC {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') :
    Finset (ι ×ₗ κ) → E'' := fun u =>
  ∑ j ∈ u, μ (pullIdx fstL a (u.filter (· ≤ j))) (pullIdx sndL b (u.filter (j ≤ ·)))

def prodFam {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (S : Finset (ι ×ₗ κ)) : Submodule k E'' :=
  Submodule.map₂ μ (A (S.image fstL)) (B (S.image sndL))

def Disjoint₂ {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') : Prop :=
  ∀ I J, Function.Injective (TensorProduct.lift (μ.compl₁₂ (A I).subtype (B J).subtype))

end Cross

end GlobalTheory.PD
