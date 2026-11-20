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
import Mathlib.RingTheory.DedekindDomain.Different
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

namespace Formalism.FourierDecayAlt.L

open NumberField

def DualIdealInclusion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = dd⁻¹ →
    ∀ (ν : ℤ) (g : ℤ), g ≠ 0 → ∀ La : FractionalIdeal (nonZeroDivisors (𝓞 E)) E,
      dd ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ 2) ≤ La →
      FractionalIdeal.spanSingleton _ (g : E) * FractionalIdeal.dual ℤ ℚ La ≤
        dd ^ (-(ν + 1)) * FractionalIdeal.spanSingleton _ ((g : E)⁻¹)

def DualLatticeInclusion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = dd⁻¹ →
    ∀ (ν : ℤ) (g : ℤ), g ≠ 0 → ∀ La : Submodule ℤ E,
      (∀ y ∈ (dd ^ ν * FractionalIdeal.spanSingleton _ ((g : E) ^ 2) :
        FractionalIdeal (nonZeroDivisors (𝓞 E)) E), y ∈ La) →
      ∀ x : E, (∀ y ∈ La, Algebra.trace ℚ E (x * y / g) ∈ (algebraMap ℤ ℚ).range) →
        x ∈ (dd ^ (-(ν + 1)) * FractionalIdeal.spanSingleton _ ((g : E)⁻¹) :
          FractionalIdeal (nonZeroDivisors (𝓞 E)) E)

end Formalism.FourierDecayAlt.L
