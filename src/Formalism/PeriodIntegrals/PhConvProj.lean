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

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhConvProj

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsFdegG (μ : Measure G) (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def coefM (σ : G → (H →L[ℂ] H)) (w : H) : G → ℂ := fun g => ⟪w, σ g w⟫_ℂ

def phOf (σ : G → (H →L[ℂ] H)) (w : H) (d : ℝ) : G → ℂ := fun g => (d : ℂ) * star (coefM σ w g)

def IsOpInt {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (μ : Measure G)
    (π : G → (K →L[ℂ] K)) (ph : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  ∀ x y : K, ⟪x, T y⟫_ℂ = ∫ g, ph g * ⟪x, π g y⟫_ℂ ∂μ

def IsRowProj {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : G → (K →L[ℂ] K)) (m : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  (∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧ T.comp T = T ∧ ∀ a, T.comp ((π a).comp T) = m a • T

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def ConvProj : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (ph m : G → ℂ), Integrable ph μ → PhConv μ ph m →
    ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] (π : G → (K →L[ℂ] K)) (T : K →L[ℂ] K),
      IsURep π → IsOpInt μ π ph T → IsRowProj π m T

end PI.PhConvProj
