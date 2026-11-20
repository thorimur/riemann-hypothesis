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

namespace Formalism.SL.NC

open Finset

def NormCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (c : K),
      |((univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = c)).card : ℝ)
          - (Fintype.card L : ℝ) ^ n / (Fintype.card K : ℝ)|
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n

def NormCharMean : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [DecidableEq K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (ψ : AddChar K ℂ), (∃ c, ψ c ≠ 1) →
    ∀ (n : ℕ) (ℓ : Fin n → L), ℓ ≠ 0 →
      ‖∑ y ∈ univ.filter (fun y : Fin n → L => ∑ i, Algebra.norm K (y i) = 0),
          ψ (∑ i, Algebra.trace K L (ℓ i * y i))‖
        ≤ (1 - 1 / (Fintype.card K : ℝ)) * (Fintype.card K : ℝ) ^ n

end Formalism.SL.NC
