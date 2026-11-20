import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

open scoped FourierTransform in
theorem UpperTheory.Lit.Cusp.fourier_zero :
    ∀ u : ℝ → ℂ, Continuous u → Integrable u →
      (∀ s : ℝ, ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * u t = 0) → ∀ t, u t = 0 := by
  intro u hc hi hz t
  have hF : 𝓕 u = 0 := by
    ext w
    rw [Real.fourier_real_eq_integral_exp_smul, Pi.zero_apply, ← hz (2 * Real.pi * w)]
    congr 1
    ext v
    rw [smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hinv := hc.fourierInv_fourier_eq hi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  simp [Real.fourierInv_eq]
