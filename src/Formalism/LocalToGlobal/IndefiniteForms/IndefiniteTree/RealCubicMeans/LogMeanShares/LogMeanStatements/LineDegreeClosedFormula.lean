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

open NumberField IsDedekindDomain

namespace Formalism.NormVectorIdentities.Items

variable (K : Type) [Field K] [NumberField K]

def degLineS (nFin : HeightOneSpectrum (𝓞 K) → ℝ) (nInf : (K →+* ℂ) → ℝ) : ℝ :=
  -((∑ᶠ la, Real.log (nFin la)) + ∑ σ : K →+* ℂ, Real.log (nInf σ)) / (Module.finrank ℚ K : ℝ)

def LineDegreeClosedFormula (nFin : HeightOneSpectrum (𝓞 K) → ℝ) (nInf : (K →+* ℂ) → ℝ) (corr : ℝ) (p q : ℕ) (logOm dK rd : ℝ) :
    Prop :=
  degLineS K nFin nInf + corr = -(((p : ℝ) - q) / 2 * logOm + (q : ℝ) * (2 * Real.log (Real.sqrt dK) - Real.log rd))

end Formalism.NormVectorIdentities.Items
