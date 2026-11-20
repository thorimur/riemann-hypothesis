import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

open MeasureTheory

noncomputable section

namespace GlobalTheory.ConvSeries

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def wt (b c : ℝ) (h : E → ℂ) (a : E) : ℂ :=
  Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a * Complex.exp (-((c * ‖a‖ ^ 2 : ℝ) : ℂ))

def innerC (a : E) : E →L[ℝ] ℂ := Complex.ofRealCLM ∘L innerSL ℝ a

def powForm (k : ℕ) (a : E) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℂ).compContinuousLinearMap fun _ => innerC a

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def coef (b c : ℝ) (h : E → ℂ) (k : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
  ∫ a, wt b c h a • powForm k a

def term (b c : ℝ) (h : E → ℂ) (k : ℕ) (y : E) : ℂ :=
  Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * (((2 * c) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) *
    coef b c h k (fun _ => y)

end GlobalTheory.ConvSeries
