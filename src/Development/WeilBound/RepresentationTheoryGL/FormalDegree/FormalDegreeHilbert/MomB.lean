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

open MeasureTheory

namespace PositivityTheory.RgFd

def MomA : Prop :=
  ∀ (Ω Ω' : Type) [MeasurableSpace Ω] [MeasurableSpace Ω'] (ν : Measure Ω) (ν' : Measure Ω') (U : Ω → ℝ) (U' : Ω' → ℝ)
    (t0 : ℕ), Measurable U → Measurable U' → (∀ x, 0 ≤ U x ∧ U x ≤ 1) → (∀ y, 0 ≤ U' y ∧ U' y ≤ 1) → 1 ≤ t0 →
    (∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * t0)) ∂ν = ∫⁻ y, ENNReal.ofReal (U' y ^ (j * t0)) ∂ν') →
    (∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * t0)) ∂ν ≠ ⊤) →
    ν {x | 0 < U x} = ν' {y | 0 < U' y}

def MomB : Prop :=
  ∀ (I : Type) [Fintype I] (α β : I → ℝ) (c : ℝ), (∀ i, 0 < α i) → (∀ i, 0 ≤ β i) → 0 ≤ c →
    ∃ (ν' : Measure (I → ℝ)) (U' : (I → ℝ) → ℝ), Measurable U' ∧ (∀ y, 0 < U' y ∧ U' y ≤ 1) ∧
      ∀ t : ℕ, ∫⁻ y, ENNReal.ofReal (U' y ^ t) ∂ν' = ENNReal.ofReal (c / ∏ i, (α i + t * β i))

def MomW : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → ENNReal) (U : Ω → ℝ) (I : Type) [Fintype I] (α β : I → ℝ)
    (c : ℝ) (t0 : ℕ), Measurable h → Measurable U → (∀ x, 0 ≤ U x ∧ U x ≤ 1) → (∀ i, 0 < α i) → (∀ i, 0 ≤ β i) → 0 ≤ c →
    (∀ t : ℕ, t0 ≤ t → ∫⁻ x, h x * ENNReal.ofReal (U x ^ t) ∂P = ENNReal.ofReal (c / ∏ i, (α i + t * β i))) →
    ∫⁻ x in {x | 0 < U x}, h x ∂P = ENNReal.ofReal (c / ∏ i, α i)

end PositivityTheory.RgFd
