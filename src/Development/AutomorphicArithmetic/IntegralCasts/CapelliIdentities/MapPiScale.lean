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

open MeasureTheory in
theorem UpperTheory.Reformulated.B.MapPiScale.map_pi_scale :
    ∀ {ι : Type} [inst : Fintype ι] {α : ι → Type}
    [inst_1 : (i : ι) → MeasurableSpace (α i)] (μ : (i : ι) → MeasureTheory.Measure (α i))
    [∀ (i : ι), MeasureTheory.SigmaFinite (μ i)] (g : (i : ι) → α i → α i),
    (∀ (i : ι), Measurable (g i)) →
      ∀ (c : ι → ENNReal),
        (∀ (i : ι), c i ≠ (0 : ENNReal)) →
          (∀ (i : ι), c i ≠ ⊤) →
            (∀ (i : ι), MeasureTheory.Measure.map (g i) (μ i) = c i • μ i) →
              MeasureTheory.Measure.map (fun (x : (i : ι) → α i) (i : ι) ↦ g i (x i)) (MeasureTheory.Measure.pi μ) =
                (∏ i : ι, c i) • MeasureTheory.Measure.pi μ := by
  intro ι _ α _ μ _ g hg c _ hc h
  have hs : ∀ i, SigmaFinite ((μ i).map (g i)) := by
    intro i
    rw [h i, ← ENNReal.coe_toNNReal (hc i)]
    exact (inferInstance : SigmaFinite ((c i).toNNReal • μ i))
  rw [Measure.pi_map_pi (fun i => (hg i).aemeasurable)]
  refine Measure.pi_eq fun s _ => ?_
  simp only [h, Measure.smul_apply, smul_eq_mul, Measure.pi_pi, Finset.prod_mul_distrib]
