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

noncomputable section

namespace PI.LocMassTypW

open MeasureTheory

theorem idx_abs {G V : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure G) [μ.IsMulLeftInvariant] (ν : Measure V) [ν.IsAddLeftInvariant]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G)) (B : AddSubgroup V)
    (hB : MeasurableSet (B : Set V)) [Countable (V ⧸ B)] (N : Set G) (C : Set V) (φ : G → V)
    (hNK : ∀ x ∈ N, ∀ k ∈ K, x * k ∈ N) (hCB : ∀ u ∈ C, ∀ b ∈ B, u + b ∈ C)
    (hφ : ∀ x ∈ N, φ x ∈ C) (hco : ∀ x ∈ N, ∀ y ∈ N, x⁻¹ * y ∈ K ↔ -φ x + φ y ∈ B)
    (hsur : ∀ u ∈ C, ∃ x ∈ N, -φ x + u ∈ B) :
    μ N * ν B = μ K * ν C := by
  classical
  have hI : ∀ q : {q : V ⧸ B | ∃ x ∈ N, (QuotientAddGroup.mk (φ x) : V ⧸ B) = q},
      ∃ x ∈ N, (QuotientAddGroup.mk (φ x) : V ⧸ B) = q := fun q => q.2
  choose x hxN hxq using hI
  have hmk : ∀ a b : V, -a + b ∈ B ↔ (QuotientAddGroup.mk a : V ⧸ B) = QuotientAddGroup.mk b :=
    fun a b => QuotientAddGroup.eq.symm
  have hC : C = ⋃ q, (fun v => -φ (x q) + v) ⁻¹' (B : Set V) := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hv
      obtain ⟨y, hy, hyB⟩ := hsur v hv
      refine ⟨⟨QuotientAddGroup.mk (φ y), y, hy, rfl⟩, ?_⟩
      rw [hmk] at hyB ⊢
      rw [hxq]
      exact hyB
    · rintro ⟨q, hq⟩
      have hc := hCB _ (hφ _ (hxN q)) _ hq
      simpa using hc
  have hN : N = ⋃ q, (fun y => (x q)⁻¹ * y) ⁻¹' (K : Set G) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hy
      refine ⟨⟨QuotientAddGroup.mk (φ y), y, hy, rfl⟩, ?_⟩
      rw [hco _ (hxN _) _ hy, hmk, hxq]
    · rintro ⟨q, hq⟩
      have hc := hNK _ (hxN q) _ hq
      simpa using hc
  have hdC : Pairwise (Function.onFun Disjoint fun q => (fun v => -φ (x q) + v) ⁻¹' (B : Set V)) := by
    intro q q' hqq
    rw [Function.onFun, Set.disjoint_left]
    intro v h1 h2
    apply hqq
    apply Subtype.ext
    simp only [Set.mem_preimage, SetLike.mem_coe, hmk] at h1 h2
    rw [← hxq q, ← hxq q', h1, h2]
  have hdN : Pairwise (Function.onFun Disjoint fun q => (fun y => (x q)⁻¹ * y) ⁻¹' (K : Set G)) := by
    intro q q' hqq
    rw [Function.onFun, Set.disjoint_left]
    intro y h1 h2
    apply hqq
    apply Subtype.ext
    simp only [Set.mem_preimage, SetLike.mem_coe] at h1 h2
    have hy : y ∈ N := by simpa using hNK _ (hxN q) _ h1
    rw [hco _ (hxN q) _ hy, hmk] at h1
    rw [hco _ (hxN q') _ hy, hmk] at h2
    rw [← hxq q, ← hxq q', h1, h2]
  have e1 : μ N = ∑' q : {q : V ⧸ B | ∃ x ∈ N, (QuotientAddGroup.mk (φ x) : V ⧸ B) = q}, μ K := by
    conv_lhs => rw [hN]
    rw [measure_iUnion hdN fun q => (measurable_const_mul _) hK]
    exact tsum_congr fun q => measure_preimage_mul μ _ _
  have e2 : ν C = ∑' q : {q : V ⧸ B | ∃ x ∈ N, (QuotientAddGroup.mk (φ x) : V ⧸ B) = q}, ν B := by
    rw [hC, measure_iUnion hdC fun q => (measurable_const_add _) hB]
    exact tsum_congr fun q => measure_preimage_add ν _ _
  rw [e1, e2, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]

end PI.LocMassTypW
