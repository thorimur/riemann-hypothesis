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

namespace GlobalTheory.PoleInertCalc

variable {K : Type} [NormedField K]

def supN {m : ℕ} (ξ : Fin m → K × K) : ℝ := ⨆ i, max ‖(ξ i).1‖ ‖(ξ i).2‖

def hQ (d : K) {m : ℕ} (ξ : Fin m → K × K) : K := ∑ i, ((ξ i).1 ^ 2 - d * (ξ i).2 ^ 2)

def rad (d : K) {m : ℕ} (ξ : Fin m → K × K) : ℝ := max (max 1 (supN ξ)) ‖hQ d ξ‖

def c0 (q s : ℝ) : ℝ := (1 - q ^ (-s)) / (1 - q ^ (1 - s))

def nIso (q : ℝ) (m : ℕ) : ℝ := q ^ (2 * (m : ℤ) - 1) + (-1) ^ m * (q ^ m - q ^ ((m : ℤ) - 1)) - 1

def primDen (q : ℝ) (m e : ℕ) : ℝ :=
  if e = 0 then 1 - q ^ (-(2 * (m : ℤ))) else nIso q m * q ^ (-(2 * (m : ℤ))) * q ^ (1 - (e : ℤ))

def shellInt (q u : ℝ) (m j : ℕ) : ℝ :=
  u ^ j * primDen q m j + ∑ e ∈ Finset.range j, (primDen q m e - primDen q m (e + 1)) * u ^ (2 * j - e)

end GlobalTheory.PoleInertCalc

end
