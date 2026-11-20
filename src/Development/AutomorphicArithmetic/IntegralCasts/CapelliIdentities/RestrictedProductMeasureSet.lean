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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open MeasureTheory in
private theorem UpperTheory.restricted_product_measure_set
    (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
    (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
    (μ : Measure G) (μi : Measure Gi) (m : ∀ v, Measure (Gv v))
    [SigmaFinite μi] [∀ v, SigmaFinite (m v)]
    (hq : Measurable q) (hp : ∀ v, Measurable (p v)) (hK : ∀ v, MeasurableSet (K v))
    (h1 : ∀ v, m v (K v) = 1) (A : Set Gi) (hA : MeasurableSet A)
    (S : Finset V) (a : NNReal)
    (h : Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
      a • μi.prod (Measure.pi fun v : S => m v)) :
    μ {g | q g ∈ A ∧ ∀ v, p v g ∈ K v} = (a : ENNReal) * μi A := by
  have hf : Measurable (fun g => (q g, fun v : S => p v g)) :=
    hq.prodMk (measurable_pi_lambda _ fun v => hp v)
  have hB : MeasurableSet (A ×ˢ (Set.univ.pi fun v : S => K v)) :=
    hA.prod (MeasurableSet.univ_pi fun v => hK v)
  have h2 := congrArg (fun ν => ν (A ×ˢ (Set.univ.pi fun v : S => K v))) h
  simp only [Measure.map_apply hf hB, Measure.restrict_apply (hf hB)] at h2
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.pi_pi] at h2
  simp only [h1, Finset.prod_const_one, mul_one] at h2
  rw [← h2]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, true_imp_iff]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨⟨ha, fun v => hb v⟩, fun v _ => hb v⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    refine ⟨ha, fun v => ?_⟩
    by_cases hv : v ∈ S
    · exact hb ⟨v, hv⟩
    · exact hc v hv

theorem UpperTheory.restricted_product_measure :
    ∀ (V G Gi : Type) (Gv : V → Type) [MeasurableSpace G] [MeasurableSpace Gi] [∀ v, MeasurableSpace (Gv v)]
        (q : G → Gi) (p : ∀ v, G → Gv v) (K : ∀ v, Set (Gv v))
        (μ : MeasureTheory.Measure G) (μi : MeasureTheory.Measure Gi) (m : ∀ v, MeasureTheory.Measure (Gv v))
        [MeasureTheory.SigmaFinite μi] [∀ v, MeasureTheory.SigmaFinite (m v)],
        Measurable q → (∀ v, Measurable (p v)) → (∀ v, MeasurableSet (K v)) → (∀ v, m v (K v) = 1) →
        (∃ A : Set Gi, MeasurableSet A ∧ μi A ≠ 0 ∧ μi A ≠ ⊤) →
        ∀ (S T : Finset V) (a b : NNReal),
          MeasureTheory.Measure.map (fun g => (q g, fun v : S => p v g)) (μ.restrict {g | ∀ v ∉ S, p v g ∈ K v}) =
            a • μi.prod (MeasureTheory.Measure.pi fun v : S => m v) →
          MeasureTheory.Measure.map (fun g => (q g, fun v : T => p v g)) (μ.restrict {g | ∀ v ∉ T, p v g ∈ K v}) =
            b • μi.prod (MeasureTheory.Measure.pi fun v : T => m v) →
          a = b := by
  intro V G Gi Gv _ _ _ q p K μ μi m _ _ hq hp hK h1 ⟨A, hA, h0, ht⟩ S T a b hS hT
  have e1 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA S a hS
  have e2 := UpperTheory.restricted_product_measure_set V G Gi Gv q p K μ μi m hq hp hK h1 A hA T b hT
  have e : (a : ENNReal) * μi A = (b : ENNReal) * μi A := e1.symm.trans e2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 e)
