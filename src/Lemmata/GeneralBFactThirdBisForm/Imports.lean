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

namespace Bl.general_b_fact_third_bis_form

theorem goal1 :
  ∀ {ι P β : Type} [inst : Fintype.{0} ι] [inst_1 : Fintype.{0} P] [inst_2 : MeasurableSpace.{0} β]
  (μ0 : MeasureTheory.Measure.{0} β) [MeasureTheory.SigmaFinite.{0} μ0],
  MeasureTheory.MeasurePreserving.{0, 0} (fun (x : ι → P → β) (p : P) (v : ι) ↦ x v p)
    (MeasureTheory.Measure.pi.{0, 0} fun (x : ι) ↦ MeasureTheory.Measure.pi.{0, 0} fun (x : P) ↦ μ0)
    (MeasureTheory.Measure.pi.{0, 0} fun (x : P) ↦ MeasureTheory.Measure.pi.{0, 0} fun (x : ι) ↦ μ0) := by
  intro ι P β _ _ _ μ0 _
  have hf : Measurable (fun (x : ι → P → β) (p : P) (v : ι) ↦ x v p) := by
    refine measurable_pi_iff.mpr fun p => measurable_pi_iff.mpr fun v => ?_
    exact (measurable_pi_apply p).comp (measurable_pi_apply v)
  refine ⟨hf, ?_⟩
  refine (MeasureTheory.Measure.pi_eq_generateFrom
    (C := fun _ => Set.pi Set.univ '' Set.pi Set.univ fun _ => {s : Set β | MeasurableSet s})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => MeasureTheory.Measure.FiniteSpanningSetsIn.pi fun _ => μ0.toFiniteSpanningSetsIn)
    ?_).symm
  intro s hs
  choose t ht hts using hs
  have hmt : ∀ p v, MeasurableSet (t p v) := fun p v => ht p v (Set.mem_univ v)
  have hs' : s = fun p => Set.pi Set.univ (t p) := funext fun p => (hts p).symm
  subst hs'
  have hpre : (fun (x : ι → P → β) (p : P) (v : ι) ↦ x v p) ⁻¹'
      Set.pi Set.univ (fun p => Set.pi Set.univ (t p)) =
      Set.pi Set.univ (fun v => Set.pi Set.univ (fun p => t p v)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    exact forall_comm
  have hmeas : MeasurableSet (Set.pi Set.univ (fun p => Set.pi Set.univ (t p))) :=
    MeasurableSet.univ_pi fun p => MeasurableSet.univ_pi fun v => hmt p v
  rw [MeasureTheory.Measure.map_apply hf hmeas, hpre, MeasureTheory.Measure.pi_pi]
  simp only [MeasureTheory.Measure.pi_pi]
  exact Finset.prod_comm

end Bl.general_b_fact_third_bis_form
