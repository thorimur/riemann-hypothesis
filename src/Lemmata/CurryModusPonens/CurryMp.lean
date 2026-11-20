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

universe u_1 u_2

namespace Bl.CurryModusPonens

open MeasureTheory in
private lemma curry_mp {ι : Type u_1} {κ : Type u_2} {X : Type} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (Function.curry : (ι × κ → X) → ι → κ → X)
      (Measure.pi fun _ : ι × κ => μ) (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ) := by
  refine ⟨(MeasurableEquiv.curry ι κ X).measurable, ?_⟩
  have h : (Measure.pi fun _ : ι × κ => μ) =
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => μ).map (MeasurableEquiv.curry ι κ X).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [MeasurableEquiv.map_apply]
    have hpre : (MeasurableEquiv.curry ι κ X).symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f
      simp [MeasurableEquiv.coe_curry_symm, Set.mem_pi, Prod.forall]
    rw [hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  rw [h]
  exact (MeasurableEquiv.curry ι κ X).map_map_symm

theorem goal1 :
  ∀ (ι : Type u_1) (κ : Type u_2) [inst : Fintype.{u_1} ι] [inst_1 : Fintype.{u_2} κ],
  @MeasureTheory.MeasurePreserving.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex) (ι → κ → Complex)
    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{max u_1 u_2, 0} (Prod.{u_1, u_2} ι κ)
        (@instFintypeProd.{u_1, u_2} ι κ inst inst_1) (fun (a : Prod.{u_1, u_2} ι κ) ↦ Complex)
        fun (i : Prod.{u_1, u_2} ι κ) ↦
        @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
          Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@MeasureTheory.MeasureSpace.toMeasurableSpace.{max u_1 u_2} (ι → κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{u_1, u_2} ι inst (fun (a : ι) ↦ κ → Complex) fun (i : ι) ↦
        @MeasureTheory.MeasureSpace.pi.{u_2, 0} κ inst_1 (fun (a : κ) ↦ Complex) fun (i : κ) ↦
          @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
            Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@Function.curry.{u_1, u_2, 1} ι κ Complex)
    (@MeasureTheory.MeasureSpace.volume.{max u_1 u_2} (Prod.{u_1, u_2} ι κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{max u_1 u_2, 0} (Prod.{u_1, u_2} ι κ)
        (@instFintypeProd.{u_1, u_2} ι κ inst inst_1) (fun (a : Prod.{u_1, u_2} ι κ) ↦ Complex)
        fun (i : Prod.{u_1, u_2} ι κ) ↦
        @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
          Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace))
    (@MeasureTheory.MeasureSpace.volume.{max u_1 u_2} (ι → κ → Complex)
      (@MeasureTheory.MeasureSpace.pi.{u_1, u_2} ι inst (fun (a : ι) ↦ κ → Complex) fun (i : ι) ↦
        @MeasureTheory.MeasureSpace.pi.{u_2, 0} κ inst_1 (fun (a : κ) ↦ Complex) fun (i : κ) ↦
          @measureSpaceOfInnerProductSpace.{0} Complex Complex.instNormedAddCommGroup instInnerProductSpaceRealComplex
            Complex.instFiniteDimensionalReal Complex.measurableSpace Complex.borelSpace)) := by
  intro ι κ _ _
  exact curry_mp _

end Bl.CurryModusPonens
