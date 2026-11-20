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

namespace Formalism.LatticeBaseChangeAlt

def FourTermSumBound : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ : ℝ), 0 ≤ d → 0 < T → 0 < ga → 0 ≤ PP → 0 ≤ D →
    0 ≤ RR ^ 2 * c + 1 / T → κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

def FourTermSumBoundOfParameters : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ q DF g₀ : ℝ), 0 ≤ d → 0 < T → T ≤ ga → 0 < PP → 1 ≤ D →
    1 ≤ RR → 0 < q → 0 ≤ C → 0 ≤ k → 0 ≤ f → 0 ≤ b → 0 < m → 0 < δ₂ →
    κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    4 * C * PP ^ 2 * D ^ 3 * k / (m * δ₂) ≤ T →
    c = RR * PP * DF ^ 2 / q → 1 ≤ g₀ → T * c * g₀ ≤ 1 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → PP ^ 2 ≤ T → 2 ≤ PP ^ 2 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

def FourTermSumBoundOfSqLe : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ q DF g₀ : ℝ), 0 ≤ d → 0 < T → T ≤ ga → 1 ≤ PP → 1 ≤ D →
    1 ≤ RR → 0 < q → 0 ≤ C → 0 ≤ k → 0 ≤ f → 0 ≤ b → 0 < m → 0 < δ₂ →
    κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    4 * C * PP ^ 2 * D ^ 3 * k / (m * δ₂) ≤ T →
    c = RR * PP * DF ^ 2 / q → 1 ≤ g₀ → T * c * g₀ ≤ 1 → PP ^ 2 ≤ f * m * b * δ₂ / 4 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → PP ^ 2 ≤ T →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

end Formalism.LatticeBaseChangeAlt
