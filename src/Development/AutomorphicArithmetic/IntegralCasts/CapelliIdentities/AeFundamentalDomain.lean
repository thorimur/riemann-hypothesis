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

theorem UpperTheory.ae_fundamental_domain :
    ∀ {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableSpace Q]
        (Γ : Subgroup G) [Countable Γ] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] (D : Set G) (π : G → Q),
        Measurable π → (∀ (γ : Γ) (g : G), π ((γ : G) * g) = π g) → (∀ g : G, ∃ γ : Γ, (γ : G) * g ∈ D) →
        ∀ p : Q → Prop, (∀ᵐ q ∂(MeasureTheory.Measure.map π (μ.restrict D)), p q) → ∀ᵐ y ∂μ, p (π y) := by
  intro G Q _ _ _ _ Γ _ μ _ D π hπ hinv hcov p hp
  rw [MeasureTheory.ae_iff] at hp ⊢
  obtain ⟨N, hsub, hNm, hN0⟩ := MeasureTheory.exists_measurable_superset_of_null hp
  rw [MeasureTheory.Measure.map_apply hπ hNm,
    MeasureTheory.Measure.restrict_apply (hπ hNm)] at hN0
  have hcover : {y | ¬ p (π y)} ⊆
      ⋃ γ : Γ, (fun g : G => (γ : G) * g) ⁻¹' (π ⁻¹' N ∩ D) := by
    intro y hy
    obtain ⟨γ, hγ⟩ := hcov y
    refine Set.mem_iUnion.2 ⟨γ, ?_, hγ⟩
    show π ((γ : G) * y) ∈ N
    rw [hinv]
    exact hsub hy
  refine MeasureTheory.measure_mono_null hcover (MeasureTheory.measure_iUnion_null fun γ => ?_)
  rw [MeasureTheory.measure_preimage_mul]
  exact hN0
