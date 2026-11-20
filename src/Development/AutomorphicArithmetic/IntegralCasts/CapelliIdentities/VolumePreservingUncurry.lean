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

theorem UpperTheory.Reformulated.B.VolumePreservingUncurry.volume_preserving_uncurry.{u_1, u_2} :
    ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype ι] [inst_1 : Fintype κ],
      @MeasureTheory.MeasurePreserving (ι → κ → Real) (Prod ι κ → Real)
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.toMeasurableSpace (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace))
        (@Function.uncurry ι κ Real)
        (@MeasureTheory.MeasureSpace.volume (ι → κ → Real)
          (@MeasureTheory.MeasureSpace.pi ι inst (fun (a : ι) ↦ κ → Real) fun (i : ι) ↦
            @MeasureTheory.MeasureSpace.pi κ inst_1 (fun (a : κ) ↦ Real) fun (i : κ) ↦ Real.measureSpace))
        (@MeasureTheory.MeasureSpace.volume (Prod ι κ → Real)
          (@MeasureTheory.MeasureSpace.pi (Prod ι κ) (@instFintypeProd ι κ inst inst_1) (fun (a : Prod ι κ) ↦ Real)
            fun (i : Prod ι κ) ↦ Real.measureSpace)) := by
  intro ι κ _ _
  have hm : Measurable (@Function.uncurry ι κ ℝ) :=
    measurable_pi_lambda _ fun p ↦ (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine ⟨hm, ?_⟩
  symm
  refine MeasureTheory.Measure.pi_eq (μ := fun _ : ι × κ ↦ (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ?_
  intro s hs
  rw [MeasureTheory.Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (@Function.uncurry ι κ ℝ) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi fun i ↦ Set.univ.pi fun k ↦ s (i, k) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall,
      Function.uncurry_apply_pair]
  rw [hpre, MeasureTheory.volume_pi_pi, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [MeasureTheory.volume_pi_pi]
