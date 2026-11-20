import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform
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

open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V]

abbrev dual (Λ : Submodule ℤ V) : Submodule ℤ V :=
  LinearMap.BilinForm.dualSubmodule (innerₗ V) Λ

def theta (Λ : Submodule ℤ V) (t : ℝ) : ℝ :=
  ∑' l : Λ, Real.exp (-Real.pi * t * ‖(l : V)‖ ^ 2)

def thetaShift (Λ : Submodule ℤ V) (t : ℝ) (x : V) : ℝ :=
  ∑' l : Λ, Real.exp (-Real.pi * t * ‖(l : V) + x‖ ^ 2)

variable (V) in

def DualIsLattice [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    DiscreteTopology (dual Λ) ∧ ∀ [DiscreteTopology (dual Λ)], IsZLattice ℝ (dual Λ)

variable (V) in

def CovolumeDual [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology (dual Λ)] [IsZLattice ℝ (dual Λ)],
    ZLattice.covolume (dual Λ) = (ZLattice.covolume Λ)⁻¹

variable (V) in

def DualDual [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ], dual (dual Λ) = Λ

variable (V) in

def PoissonDecay [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ), Continuous f →
    ∀ b : ℝ, (Module.finrank ℝ V : ℝ) < b →
    f =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    (𝓕 f : V → ℂ) =O[cocompact V] (fun v => ‖v‖ ^ (-b)) →
    ∀ x : V,
      Summable (fun μ : dual Λ =>
          (𝓕 f : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
      HasSum (fun l : Λ => f ((l : V) + x))
        ((ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
          (𝓕 f : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))

variable (V) in

def PoissonSchwartz [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : 𝓢(V, ℂ)) (x : V),
      Summable (fun μ : dual Λ =>
          (𝓕 (f : V → ℂ) : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
      HasSum (fun l : Λ => f ((l : V) + x))
        ((ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ,
          (𝓕 (f : V → ℂ) : V → ℂ) μ * Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)))

variable (V) in

def ThetaSummable [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (t : ℝ), 0 < t → ∀ x : V,
    Summable (fun l : Λ => Real.exp (-Real.pi * t * ‖(l : V) + x‖ ^ 2))

variable (V) in
def ThetaPos [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (t : ℝ), 0 < t → 1 ≤ theta Λ t

variable (V) in

def ThetaInversion [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (t : ℝ), 0 < t →
    theta Λ (1 / t) =
      (ZLattice.covolume Λ)⁻¹ * t ^ ((Module.finrank ℝ V : ℝ) / 2) * theta (dual Λ) t

variable (V) in

def ThetaShiftInversion [FiniteDimensional ℝ V] : Prop :=
  ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (t : ℝ), 0 < t → ∀ x : V,
    Summable (fun μ : dual Λ => (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))) ∧
    (thetaShift Λ t x : ℂ) =
      (ZLattice.covolume Λ : ℂ)⁻¹ * ((t ^ (-(Module.finrank ℝ V : ℝ) / 2) : ℝ) : ℂ) *
        ∑' μ : dual Λ, (Real.exp (-Real.pi * ‖(μ : V)‖ ^ 2 / t) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ))

end Formalism.H
