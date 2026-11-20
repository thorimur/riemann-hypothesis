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

namespace Formalism.SL.MV

open Finset

noncomputable def kern {ι Mv : Type} [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (i j : ι) : ℝ :=
  ∑ m ∈ univ.filter (fun m => src m = i ∧ tgt m = j), μ m

def MoveKernel : Prop :=
  ∀ (ι Mv : Type) [Fintype ι] [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (inv : Mv → Mv),
    (∀ m, inv (inv m) = m) → (∀ m, src (inv m) = tgt m) → (∀ m, tgt (inv m) = src m) → (∀ m, μ (inv m) = μ m) →
    ∀ i j, kern src tgt μ i j = kern src tgt μ j i

def MoveBound : Prop :=
  ∀ (ι Mv : Type) [Fintype ι] [Fintype Mv] [DecidableEq ι] (src tgt : Mv → ι) (μ : Mv → ℝ) (inv : Mv → Mv)
    (w : ι → ℂ) (χ : Mv → ℂ) (ε₁ ε₂ : ℝ),
    (∀ m, inv (inv m) = m) → (∀ m, src (inv m) = tgt m) → (∀ m, tgt (inv m) = src m) → (∀ m, μ (inv m) = μ m) →
    (∀ m, w (tgt m) = w (src m) * χ m) →
    (∀ i, ‖w i‖ ≤ 1) →
    (∀ i, |(∑ m ∈ univ.filter (fun m => src m = i), μ m) - 1| ≤ ε₁) →
    (∀ i, ‖∑ m ∈ univ.filter (fun m => src m = i), (μ m : ℂ) * χ m‖ ≤ ε₂) →
    ‖∑ i, w i‖ ≤ (ε₁ + ε₂) * (Fintype.card ι : ℝ)

end Formalism.SL.MV
