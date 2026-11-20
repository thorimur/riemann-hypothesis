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
import Mathlib.Order.CompletePartialOrder
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

namespace MeasureEqCardCosetsMul
end MeasureEqCardCosetsMul

theorem UpperTheory.Reformulated.B.Yla7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]
      [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] {I : Subgroup G},
      IsOpen (↑I : Set G) →
        ∀ {D : Set G},
          (∀ g ∈ D, ∀ i ∈ I, g * i ∈ D) →
            ∀ (S : Finset (G ⧸ I)),
              (∀ (q : G ⧸ I), q ∈ S ↔ Quotient.out q ∈ D) →
                (μ : Set G → ENNReal) D = (↑S.card : ENNReal) * (μ : Set G → ENNReal) (↑I : Set G) := by
  intro G _ _ _ _ _ μ _ I hI D hD S hS
  classical
  set f : G ⧸ I → Set G := fun q => (fun h => (Quotient.out q)⁻¹ * h) ⁻¹' (I : Set G) with hf
  have hmem : ∀ q x, x ∈ f q ↔ (Quotient.out q)⁻¹ * x ∈ I := fun q x => Iff.rfl
  have hmk : ∀ q x, x ∈ f q → (QuotientGroup.mk x : G ⧸ I) = q := by
    intro q x hx
    rw [hmem] at hx
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ I) = QuotientGroup.mk x :=
      QuotientGroup.eq.mpr hx
    rw [← this]
    exact Quotient.out_eq' q
  have hDeq : D = ⋃ q ∈ S, f q := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk x : G ⧸ I), ?_, ?_⟩
      · rw [hS]
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I x
        rw [hh]
        exact hD x hx h h.2
      · rw [hmem]
        have : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ I)) : G ⧸ I) = QuotientGroup.mk x :=
          Quotient.out_eq' _
        exact QuotientGroup.eq.mp this
    · rintro ⟨q, hq, hx⟩
      rw [hmem] at hx
      have h1 := hD _ ((hS q).mp hq) _ hx
      simpa using h1
  have hdisj : (S : Set (G ⧸ I)).PairwiseDisjoint f := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    exact hab ((hmk a x hxa).symm.trans (hmk b x hxb))
  have hmeas : ∀ q ∈ S, MeasurableSet (f q) := by
    intro q _
    exact (hI.preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hDeq, MeasureTheory.measure_biUnion_finset hdisj hmeas]
  have : ∀ q ∈ S, μ (f q) = μ (I : Set G) := by
    intro q _
    exact MeasureTheory.measure_preimage_mul μ _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
