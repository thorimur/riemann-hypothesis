import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Matrix.ColumnRowPartitioned
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

open scoped NNReal

namespace GlobalTheory.EisGen

variable {G : Type} [TopologicalSpace G]

def LocReg (ht : G → ℝ≥0) (Ei : ℂ → G → ℂ) : Prop :=
  ∀ s₀ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → G → ℂ), 0 < r ∧
    (∀ s ∈ Metric.ball s₀ r, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Ei s g) ∧
    (∀ g, DifferentiableOn ℂ (fun s => H s g) (Metric.ball s₀ r)) ∧
    ContinuousOn (fun x : ℂ × G => H x.1 x.2) (Metric.ball s₀ r ×ˢ Set.univ) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ s ∈ Metric.ball s₀ r, ∀ g, ‖H s g‖ ≤ C * (ht g : ℝ) ^ N

def ContFrom (ht : G → ℝ≥0) (σ₀ : ℝ) (e : ℂ → G → ℂ) : Prop :=
  ∃ Ei : ℂ → G → ℂ, (∀ s : ℂ, σ₀ < s.re → ∀ g, Ei s g = e s g) ∧ LocReg ht Ei

theorem ContFrom.mono {ht : G → ℝ≥0} {σ₀ σ₁ : ℝ} {e : ℂ → G → ℂ} (h : ContFrom ht σ₀ e) (hσ : σ₀ ≤ σ₁) : ContFrom ht σ₁ e :=
  let ⟨Ei, h1, h2⟩ := h
  ⟨Ei, fun s hs => h1 s (hσ.trans_lt hs), h2⟩

variable (E : Type) [Field E] (n : ℕ) in

def diagCols : Matrix (Fin (n + n)) (Fin n) E :=
  (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) E) (1 : Matrix (Fin n) (Fin n) E)).submatrix finSumFinEquiv.symm id

end GlobalTheory.EisGen

end
