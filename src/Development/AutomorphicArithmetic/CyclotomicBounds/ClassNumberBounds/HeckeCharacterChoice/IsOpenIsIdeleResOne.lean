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

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.Choice

open KStar.IdealValuations

variable {E : Type*} [Field E] [NumberField E] {𝔪 : Ideal (𝓞 E)}

private noncomputable def resExp (𝔪 : Ideal (𝓞 E)) (v : HeightOneSpectrum (𝓞 E)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔪).factors

private theorem finite_above (h𝔪 : 𝔪 ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 E) | 𝔪 ≤ v.asIdeal}.Finite := by
  simpa only [Ideal.dvd_iff_le] using Ideal.finite_factors h𝔪

end KStar.Choice
