import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open SchwartzMap

namespace GlobalTheory

theorem dense_schwartz_mul_of_ne_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (g : SchwartzMap V ℂ) (hg : ∀ x, g x ≠ 0)
    (hd : Dense {φ : SchwartzMap V ℂ | HasCompactSupport (⇑φ)}) :
    Dense {F : SchwartzMap V ℂ | ∃ ψ : SchwartzMap V ℂ, ∀ x, F x = ψ x * g x} := by
  refine hd.mono ?_
  intro φ hφ
  have hφ' : HasCompactSupport (⇑φ) := hφ
  have hinv : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x)⁻¹) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have h1 : ContDiffAt ℂ (⊤ : ℕ∞) (fun z : ℂ => z⁻¹) (g x) := contDiffAt_inv ℂ (hg x)
    exact (h1.restrict_scalars ℝ).comp x (g.smooth ⊤).contDiffAt
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * (g x)⁻¹) := (φ.smooth ⊤).mul hinv
  have hc : HasCompactSupport (fun x => φ x * (g x)⁻¹) := hφ'.mul_right
  refine ⟨hc.toSchwartzMap hs, fun x => ?_⟩
  change φ x = φ x * (g x)⁻¹ * g x
  rw [mul_assoc, inv_mul_cancel₀ (hg x), mul_one]

end GlobalTheory
