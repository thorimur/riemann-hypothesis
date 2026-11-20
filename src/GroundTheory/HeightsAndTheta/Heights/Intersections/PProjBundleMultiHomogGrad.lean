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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section Graded

variable {σ τ R M : Type*} [CommRing R] [AddCommMonoid M]

theorem aeval_weightedHomogeneousComponent_of_weights (w : σ → M) (ω : τ → M)
    (e : σ → MvPolynomial τ R) (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) (m : M)
    (p : MvPolynomial σ R) :
    aeval e (weightedHomogeneousComponent w m p) = weightedHomogeneousComponent ω m (aeval e p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous ω (aeval e (monomial d c)) (Finsupp.weight w d) := by
      rw [aeval_monomial, Finsupp.weight_apply, algebraMap_eq]
      have := (isWeightedHomogeneous_C ω c).mul (IsWeightedHomogeneous.prod d.support
        (fun v => e v ^ d v) (fun v => d v • w v) (fun v _ => (he v).pow (d v)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight w d = m
    · have hmon' : IsWeightedHomogeneous ω (aeval e (monomial d c)) m := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial w d c
        (m := Finsupp.weight w d) rfl).weightedHomogeneousComponent_ne m
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne m (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem isWeightedHomogeneous_aeval_of_weights {w : σ → M} {ω : τ → M} {e : σ → MvPolynomial τ R}
    (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v)) {p : MvPolynomial σ R} {a : M}
    (hp : IsWeightedHomogeneous w p a) : IsWeightedHomogeneous ω (aeval e p) a := by
  rw [← hp.weightedHomogeneousComponent_same, aeval_weightedHomogeneousComponent_of_weights w ω e he]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem weightedHomogeneousComponent_mem_map_aeval [DecidableEq M] {w : σ → M} {ω : τ → M}
    {e : σ → MvPolynomial τ R} (he : ∀ v, IsWeightedHomogeneous ω (e v) (w v))
    (G : Set (MvPolynomial σ R)) (hG : ∀ f ∈ G, ∃ a, IsWeightedHomogeneous w f a)
    {f : MvPolynomial τ R} (hf : f ∈ Ideal.map (aeval e) (Ideal.span G)) (m : M) :
    weightedHomogeneousComponent ω m f ∈ Ideal.map (aeval e) (Ideal.span G) := by
  let _ := weightedGradedAlgebra R ω
  have hom : (Ideal.map (aeval e) (Ideal.span G)).IsHomogeneous (weightedHomogeneousSubmodule R ω) := by
    rw [Ideal.map_span]
    refine Ideal.homogeneous_span _ _ fun x hx => ?_
    obtain ⟨f, hfG, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hG f hfG
    exact ⟨a, (mem_weightedHomogeneousSubmodule R ω a _).mpr (isWeightedHomogeneous_aeval_of_weights he ha)⟩
  exact weightedHomogeneousComponent_mem_of_mem R ω hom hf m

theorem weightedHomogeneousComponent_mul_of_left {M : Type*} [AddCancelCommMonoid M] {w : σ → M}
    {c : MvPolynomial σ R} {m : M} (hc : IsWeightedHomogeneous w c m) (γ : M) (L : MvPolynomial σ R) :
    weightedHomogeneousComponent w (γ + m) (c * L) = c * weightedHomogeneousComponent w γ L := by
  classical
  induction L using MvPolynomial.induction_on' with
  | monomial d r =>
    have hd := isWeightedHomogeneous_monomial w d r (m := Finsupp.weight w d) rfl
    have hcd := hc.mul hd
    by_cases hdm : Finsupp.weight w d = γ
    · rw [(hdm ▸ hd : IsWeightedHomogeneous w (monomial d r) γ).weightedHomogeneousComponent_same]
      rw [show γ + m = m + Finsupp.weight w d by rw [hdm, add_comm]]
      exact hcd.weightedHomogeneousComponent_same
    · rw [hd.weightedHomogeneousComponent_ne γ (Ne.symm hdm), mul_zero]
      refine hcd.weightedHomogeneousComponent_ne _ fun h => hdm ?_
      rw [add_comm m] at h
      exact (add_right_cancel h).symm
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]

end Graded

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
