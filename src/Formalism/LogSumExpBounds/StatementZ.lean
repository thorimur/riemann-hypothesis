import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace Formalism.NuclearRankWeightBounds.Z

open Finset

def LatSum : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ) (S : Finset (Fin f → ℂ)),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ o ∈ S, o ∈ La ∧ o ≠ 0) →
      ∑ o ∈ S, ∏ v, min 1 ((x v / ‖o v‖) ^ K)
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2)

def ZLift : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ) (La : AddSubgroup (Fin f → ℂ)) (x : Fin f → ℝ) (K : ℕ)
      (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (Z : Finset (Fin f → ℂ)) (U : (Fin f → ℂ) → H) (B : ℝ),
      (∀ o ∈ La, o ≠ 0 → 1 ≤ ∏ v, ‖o v‖) → (∀ v, 0 < x v) → ∏ v, x v < 1 → 3 ≤ K →
      (∀ z ∈ Z, ∀ v, z v ≠ 0) →
      (∀ z ∈ Z, ∀ z' ∈ Z, (fun v => (z v)⁻¹ - (z' v)⁻¹) ∉ La → inner ℂ (U z) (U z') = 0) →
      (∀ A : Finset (Fin f),
        ∑ z ∈ Z, (∏ v ∈ A, (2 / (x v * ‖z v‖)) ^ (2 * K)) * ‖U z‖ ^ 2 ≤ B) →
      ∑ z ∈ Z, ∑ z' ∈ Z.erase z, ‖inner ℂ (U z) (U z')‖
        ≤ C ^ f * (∏ v, x v) ^ ((K : ℝ) - 5 / 2) * B

end Formalism.NuclearRankWeightBounds.Z
