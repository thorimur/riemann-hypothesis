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

noncomputable section

namespace PI.UnipVal

variable {K : Type} [Field K] [NumberField K]

def vw (w : HeightOneSpectrum (𝓞 K)) (a : K) : ℤ :=
  FractionalIdeal.count K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a)

def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)

def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)

def UnipVal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)),
    (∀ n : ℕ, n ≠ 0 → vw w ((n : ℕ) : K) = ramw w * (padicValNat (plc w) n : ℤ)) ∧
    ∀ g₁ g₂ a : ℕ, g₁.Prime → g₂.Prime → g₁ ≠ g₂ →
      (vw w (((g₁ ^ a * g₂ ^ a : ℕ)) : K) : ℝ) = (ramw w : ℝ) * (if plc w = g₁ ∨ plc w = g₂ then (a : ℝ) else 0)

end PI.UnipVal

end
