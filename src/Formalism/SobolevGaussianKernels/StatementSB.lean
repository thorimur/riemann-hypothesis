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

namespace Formalism.SL.SB

open MeasureTheory
open scoped ContDiff

noncomputable def pd {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  fun y => fderiv ℝ g y (Pi.single i 1)

noncomputable def mixed {n : ℕ} (α : Finset (Fin n)) (g : (Fin n → ℝ) → ℂ) : (Fin n → ℝ) → ℂ :=
  (α.sort (· ≤ ·)).foldr pd g

def cube {n : ℕ} (a : Fin n → ℝ) (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (a i) (a i + δ))

def SobolevN : Prop :=
  ∀ (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (a : Fin n → ℝ) (δ : ℝ),
    ContDiff ℝ ∞ φ → 0 < δ →
    ∀ x ∈ cube a δ,
      ‖φ x‖ ^ 2 ≤ 2 ^ n / δ ^ n *
        ∫ y in cube a δ, (∑ α : Finset (Fin n), δ ^ (2 * α.card) * ‖mixed α φ y‖ ^ 2)

end Formalism.SL.SB
