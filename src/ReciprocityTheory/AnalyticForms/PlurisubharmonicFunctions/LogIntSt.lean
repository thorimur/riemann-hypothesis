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

namespace ReciprocityTheory.AnForm.A

open MeasureTheory

noncomputable section

def logMono {D : ℕ} (m : Fin D → ℤ) (z : Fin D → ℂ) : ℝ :=
  ∑ i, (m i : ℝ) * Real.log ‖z i‖

def LogNormLocIntCStatement : Prop :=
  LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume

def LogCoordLocIntStatement : Prop :=
  ∀ (D : ℕ) (i : Fin D), LocallyIntegrable (fun z : Fin D → ℂ => Real.log ‖z i‖) volume

def LogMonoLocIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ), LocallyIntegrable (logMono m) volume

def LogMonoTestIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ) (f : (Fin D → ℂ) → ℝ), Continuous f → HasCompactSupport f →
    Integrable (fun z => f z * logMono m z) volume

def LogUnitMonoLocIntStatement : Prop :=
  ∀ (D : ℕ) (m : Fin D → ℤ) (U : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℂ), IsOpen U →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    LocallyIntegrableOn (fun z => Real.log ‖u z * ∏ i, z i ^ m i‖) U volume

end

end ReciprocityTheory.AnForm.A
