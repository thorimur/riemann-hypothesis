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

theorem UpperTheory.Reformulated.B.Qk59.sq_shift :
    ∀ {G : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G]
    {μ : MeasureTheory.Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) D μ →
      ∀ {f : G → ℝ},
        (∀ γ ∈ Γ, ∀ (y : G), f (γ * y) = f y) → ∀ (g : G), ∫ (y : G) in D, f (y * g) ∂μ = ∫ (y : G) in D, f y ∂μ := by
  intro G _ _ _ _ _ μ _ _ Γ _ D hD f hf g
  have hD' : MeasureTheory.IsFundamentalDomain (↥Γ) ((fun y : G => y * g⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv
      (MeasureTheory.measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id
      (fun γ y => by
        show ((γ : G) * y) * g⁻¹ = (γ : G) * (y * g⁻¹)
        exact mul_assoc _ _ _)
  have h1 := (MeasureTheory.measurePreserving_mul_right μ g).setIntegral_preimage_emb
    (measurableEmbedding_mulRight g) f ((fun y : G => y * g⁻¹) ⁻¹' D)
  have h2 : (fun y : G => y * g) ⁻¹' ((fun y : G => y * g⁻¹) ⁻¹' D) = D := by
    ext y
    simp
  rw [h2] at h1
  rw [h1]
  exact hD'.setIntegral_eq hD (fun γ y => hf γ γ.2 y)
