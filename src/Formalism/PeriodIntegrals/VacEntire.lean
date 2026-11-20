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

noncomputable section

namespace PI.VacEntire

variable {ι : Type} [Fintype ι] {N N' : ℕ}

def Hf (A : ℝ) (z w : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)

def al (d : ℕ) (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (Hf A x x).re))

def U (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf A z x - (Real.pi : ℂ) * Hf A x x / 2)

def Iop (d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al d A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) * U A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) G z

def tensPow {n : Type} [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) : ℂ :=
  ∏ i : Fin N', ∏ j : Fin N, θ fun τ => z τ i j

def IopEntire : Prop :=
  ∀ (ι : Type) [Fintype ι] (N N' d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ), AnalyticOnNhd ℂ G Set.univ → AnalyticOnNhd ℂ (Iop d A La₁ La₂ G) Set.univ

def TensEntire : Prop :=
  ∀ (n : Type) [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ), AnalyticOnNhd ℂ θ Set.univ →
    AnalyticOnNhd ℂ (tensPow θ N N') Set.univ

def Target : Prop := IopEntire ∧ TensEntire

end PI.VacEntire
