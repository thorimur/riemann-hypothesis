import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Taut

def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2 - 8 * x)

def oscS (u : ℂ) : ℝ := Real.sin ((-1 / 2) * Real.log (‖u‖ ^ 2))

def oscW (u : ℂ) : ℝ := cutoff (‖u‖ ^ 2) * oscS u

theorem contDiff_cutoffN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun u : ℂ => cutoff (‖u‖ ^ 2) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition := Real.smoothTransition.contDiff
  exact h1.comp ((contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))))

theorem contDiffAt_oscS {u : ℂ} (hu : u ≠ 0) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) oscS u := by
  have hne : ‖u‖ ^ 2 ≠ 0 := by positivity
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v : ℂ => Real.log (‖v‖ ^ 2)) u :=
    (contDiff_norm_sq ℝ).contDiffAt.log hne
  exact Real.contDiff_sin.contDiffAt.comp u (contDiffAt_const.mul h1)

theorem contDiffAt_oscW {u : ℂ} (hu : u ≠ 0) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) oscW u :=
  contDiff_cutoffN.contDiffAt.mul (contDiffAt_oscS hu)

end GroundTheory.Heights₂.Heights.LowerBoundFree.Taut
