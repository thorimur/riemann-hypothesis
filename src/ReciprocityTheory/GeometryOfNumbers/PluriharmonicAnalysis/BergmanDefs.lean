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

namespace ReciprocityTheory.GeometryOfNumbersTheory

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

def bGram (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ∫ x, starRingEnd ℂ (s i x) * s j x * (w x : ℂ) ∂μ

def bNormSq (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (c : Fin r → ℂ) : ℝ :=
  ∫ x, ‖∑ i, c i * s i x‖ ^ 2 * w x ∂μ

def bergmanDensity (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ) (x : X) : ℝ :=
  w x * (∑ i, ∑ j, (bGram μ s w)⁻¹ i j * s i x * starRingEnd ℂ (s j x)).re

end ReciprocityTheory.GeometryOfNumbersTheory
