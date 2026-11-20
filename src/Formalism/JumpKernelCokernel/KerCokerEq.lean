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

namespace Formalism.KernelCokernelLengths

def KerCokerEq : Prop :=
  ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M], Module.length O M ≠ ⊤ →
    ∀ f : Module.End O M, Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f)

def CokerSurj : Prop :=
  ∀ (O : Type) [CommRing O] (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M']
    [Module O M'] (f : Module.End O M) (f' : Module.End O M') (g : M →ₗ[O] M'),
    Function.Surjective g → g ∘ₗ f = f' ∘ₗ g →
      Module.length O (M' ⧸ LinearMap.range f') ≤ Module.length O (M ⧸ LinearMap.range f)

end Formalism.KernelCokernelLengths
