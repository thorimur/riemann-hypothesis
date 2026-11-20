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
import Mathlib.NumberTheory.Padics.PadicIntegers
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

namespace UpperTheory.V.PropA

variable (l : ℕ) [Fact l.Prime]

def GenBy (R : ℕ) (X : Type) [AddCommGroup X] [Module ℤ_[l] X] : Prop :=
  ∃ π : (Fin R → ℤ_[l]) →ₗ[ℤ_[l]] X, Function.Surjective π

abbrev jZero (l R : ℕ) : ℕ := Nat.log l R + 3

abbrev vl (x : ℤ_[l]) : ℕ∞ := IsDiscreteValuationRing.addVal ℤ_[l] x

def IsLevel (u : ℤ_[l]) (c : ℕ) : Prop := vl l (u - 1) = c ∧ 1 ≤ c ∧ (l = 2 → 2 ≤ c)

variable {l} {X : Type} [AddCommGroup X] [Module ℤ_[l] X]

def cokLen (f : Module.End ℤ_[l] X) : ℕ∞ := Module.length ℤ_[l] (X ⧸ LinearMap.range f)

def InPow (k : ℕ) (f : Module.End ℤ_[l] X) : Prop := ∀ x : X, ∃ y : X, f x = (l : ℤ_[l]) ^ k • y

def Unip (γ : Module.End ℤ_[l] X) : Prop := ∃ N : ℕ, InPow 1 ((γ - 1) ^ N)

def twLen (γ : Module.End ℤ_[l] X) (u : ℤ_[l]) (e m : ℕ) : ℕ∞ := cokLen ((u ^ e • γ) ^ l ^ m - 1)

theorem cokLen_le_of_range_le {f g : Module.End ℤ_[l] X} (h : LinearMap.range g ≤ LinearMap.range f) :
    cokLen f ≤ cokLen g :=
  Module.length_le_of_surjective (Submodule.factor h) (Submodule.factor_surjective h)

end UpperTheory.V.PropA

end
