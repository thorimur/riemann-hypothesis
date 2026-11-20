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

open MeasureTheory

noncomputable section
namespace GlobalTheory.ThK.Dbl

def IsAut {G : Type} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (f : G → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) ∧ ∃ U : Subgroup G, IsOpen (U : Set G) ∧
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => fun x => f (x * u)))

def opT {G : Type} [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (k : G → G → ℂ) (φ : G → ℂ) : G → ℂ :=
  fun h => ∫ h' in 𝓕, φ h' * k h h' ∂μ

def rconv {G : Type} [Mul G] [MeasurableSpace G] (μ : Measure G) (ψ : G → ℂ) (φ : G → ℂ) : G → ℂ :=
  fun h => ∫ g, ψ g * φ (h * g) ∂μ

def InSpan {G : Type} [Mul G] (f f' u u' : G → ℂ) : Prop :=
  ∃ (n : ℕ) (y : Fin n → G) (c : Fin n → ℂ),
    u = (fun h => ∑ j, c j * f (h * y j)) ∧ u' = (fun h => ∑ j, c j * f' (h * y j))

end GlobalTheory.ThK.Dbl
