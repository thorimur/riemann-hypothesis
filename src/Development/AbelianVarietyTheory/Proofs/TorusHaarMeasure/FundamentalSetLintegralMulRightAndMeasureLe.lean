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
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Topology.Sheaves.Presheaf
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem fundamentalSet_lintegral_mul_right_and_measure_le :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) := by
  intro G _ _ _ _ _ _ _ _ ν _ Γ _ F hF hex
  have hFD : IsFundamentalDomain Γ F ν :=
    IsFundamentalDomain.mk' hF.nullMeasurableSet (fun g => hex g)
  refine ⟨?_, ?_⟩
  · intro h hh φ hφ hinv
    have hmeas : MeasurableSet {g : G | g * h⁻¹ ∈ F} := (measurable_mul_const h⁻¹) hF
    have hFD' : IsFundamentalDomain Γ {g : G | g * h⁻¹ ∈ F} ν := by
      refine IsFundamentalDomain.mk' hmeas.nullMeasurableSet (fun g => ?_)
      have := hex (g * h⁻¹)
      simpa [Subgroup.smul_def, mul_assoc] using this
    have h1 : ∫⁻ g in {g : G | g * h⁻¹ ∈ F}, φ g ∂ν = ∫⁻ g in F, φ (g * h) ∂ν := by
      conv_lhs => rw [← hh]
      rw [setLIntegral_map hmeas hφ (measurable_mul_const h)]
      congr 2
      ext g
      simp
    rw [← h1]
    exact hFD'.setLIntegral_eq hFD φ (fun γ g => hinv γ γ.2 g)
  · intro K hK
    rw [hFD.measure_eq_tsum K]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro g ⟨hg, γ, hγ, k, hk, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hg⟩

end GlobalTheory
