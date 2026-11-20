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

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

def gW (d : ℕ) (α : Type) [Fintype α] (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2))

def zeroCnt {X : Type} (d : ℕ) {α : Type} [Fintype α] (A : Set X) (b : α → X → ℂ)
    (C : Fin d → α → ℂ) : ℝ≥0∞ :=
  (({z ∈ A | ∀ k, ∑ j, C k j * b j z = 0}.encard : ℕ∞) : ℝ≥0∞)

def fsLevi {β : Type} [Fintype β] {d : ℕ} (f : β → ℂ) (F : Matrix β (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a c =>
    (((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) * ∑ j, F j a * conj (F j c) -
        (∑ j, F j a * conj (f j)) * ∑ j, f j * conj (F j c)) /
      ((1 + ∑ j, ‖f j‖ ^ 2 : ℝ) : ℂ) ^ 2

def joinCol {d : ℕ} {α : Type} [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) : Fin d → α → ℂ :=
  fun k j => if h : j = j₀ then c k else C k ⟨j, h⟩

end GlobalTheory.CompanionTheory.FSCrofton
