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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

abbrev V (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

def IsTest {n : ℕ} (Ω : Set (V n)) (g : V n → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ω

noncomputable def dbarDir {n : ℕ} (g : V n → ℂ) (z v : V n) : ℂ :=
  fderiv ℝ g z (I • v) - I * fderiv ℝ g z v

def WeakHolo {n : ℕ} (Ω : Set (V n)) (u : V n → ℂ) : Prop :=
  LocallyIntegrableOn u Ω volume ∧
    ∀ g : V n → ℂ, IsTest Ω g → ∀ v : V n, ∫ z in Ω, u z * dbarDir g z v = 0

def HoloWeakStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (u : V n → ℂ),
    IsOpen Ω → DifferentiableOn ℂ u Ω → WeakHolo Ω u

def RegStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (u : V n → ℂ),
    IsOpen Ω → WeakHolo Ω u →
      ∃ U : V n → ℂ, DifferentiableOn ℂ U Ω ∧ u =ᵐ[volume.restrict Ω] U

def MVStatement : Prop :=
  ∀ (n : ℕ) (c : V n) (R : ℝ) (u : V n → ℂ) (r : ℝ → ℝ≥0∞),
    DifferentiableOn ℂ u (ball c R) → Measurable r →
      ‖u c‖ₑ ^ 2 * ∫⁻ z in ball c R, r ‖z - c‖ ≤ ∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖

def MVEqStatement : Prop :=
  ∀ (n : ℕ) (c : V n) (R : ℝ) (u : V n → ℂ) (k : ℝ → ℝ),
    DifferentiableOn ℂ u (ball c R) →
    IntegrableOn (fun z => (k ‖z - c‖ : ℂ)) (ball c R) →
    IntegrableOn (fun z => u z * (k ‖z - c‖ : ℂ)) (ball c R) →
      ∫ z in ball c R, u z * (k ‖z - c‖ : ℂ) = u c * ∫ z in ball c R, (k ‖z - c‖ : ℂ)

def MVDivStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    Tendsto (fun δ : ℝ => ∫⁻ z in ball (0 : V n) 1, ENNReal.ofReal ((‖z‖ ^ 2 + δ) ^ (-(n : ℝ))))
      (𝓝[>] 0) (𝓝 ∞)

def MVPowStatement : Prop :=
  ∀ (n : ℕ) (s : ℝ), 0 < n →
    (IntegrableOn (fun z : V n => ‖z‖ ^ (-2 * s)) (ball 0 1) ↔ s < n)

def ExtWeakStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (F u : V n → ℂ),
    IsOpen Ω → DifferentiableOn ℂ F Ω →
    DifferentiableOn ℂ u (Ω \ {z | F z = 0}) →
    IntegrableOn (fun z => ‖u z‖ ^ 2) (Ω \ {z | F z = 0}) →
      WeakHolo Ω ((Ω \ {z | F z = 0}).indicator u)

def ExtStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (F u : V n → ℂ),
    IsOpen Ω → DifferentiableOn ℂ F Ω →
    DifferentiableOn ℂ u (Ω \ {z | F z = 0}) →
    IntegrableOn (fun z => ‖u z‖ ^ 2) (Ω \ {z | F z = 0}) →
      ∃ U : V n → ℂ, DifferentiableOn ℂ U Ω ∧ EqOn U u (Ω \ {z | F z = 0})

def ExtNullStatement : Prop :=
  ∀ (n : ℕ) (c : V n) (R : ℝ) (F : V n → ℂ),
    DifferentiableOn ℂ F (ball c R) → (∃ z ∈ ball c R, F z ≠ 0) →
      volume (ball c R ∩ {z | F z = 0}) = 0

def IdentStatement : Prop :=
  ∀ (n : ℕ) (Ω : Set (V n)) (F : V n → ℂ) (a : V n),
    IsOpen Ω → Convex ℝ Ω → DifferentiableOn ℂ F Ω → a ∈ Ω → F =ᶠ[𝓝 a] 0 → EqOn F 0 Ω

theorem isTest_zero {n : ℕ} (Ω : Set (V n)) : IsTest Ω (fun _ => 0) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩

end ReciprocityTheory.L2DbarEstimates.C
