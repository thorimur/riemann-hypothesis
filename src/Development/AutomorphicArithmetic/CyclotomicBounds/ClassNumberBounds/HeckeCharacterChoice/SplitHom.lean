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

open NumberField

namespace KStar.Choice

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {p : ℕ}

def homsOver (E : Type*) [Field E] [Algebra K E] (ψ : 𝓞 K →+* ZMod p) :
    Set (𝓞 E →+* ZMod p) :=
  {φ | φ.comp (algebraMap (𝓞 K) (𝓞 E)) = ψ}

def conjHom (φ : 𝓞 E →+* ZMod p) (σ : E ≃ₐ[K] E) : 𝓞 E →+* ZMod p :=
  φ.comp (RingOfIntegers.mapRingHom (σ : E →+* E))

private theorem ker_isPrime {R : Type*} [CommRing R] (hp : p.Prime) (f : R →+* ZMod p) :
    (RingHom.ker f).IsPrime := by
  have := Fact.mk hp
  exact RingHom.ker_isPrime f

end KStar.Choice
