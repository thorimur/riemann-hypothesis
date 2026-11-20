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

noncomputable def UpperTheory.Reformulated.B.Qk18.PolyIn :
    {R : Type} → [inst : Ring R] → [Algebra ℂ R] → (ℂ → R) → ℕ → Prop :=
    fun {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ) ↦
      ∃ (a : ℕ → R), ∀ (s : ℂ), f s = ∑ k ∈ Finset.range (d + (1 : ℕ)), s ^ k • a k

theorem UpperTheory.Reformulated.B.Qk18.polyIn_mul :
    ∀ {R : Type} [inst : Ring R] [inst_1 : Algebra ℂ R] {f g : ℂ → R} {d₁ d₂ : ℕ},
      UpperTheory.Reformulated.B.Qk18.PolyIn f d₁ →
        UpperTheory.Reformulated.B.Qk18.PolyIn g d₂ → UpperTheory.Reformulated.B.Qk18.PolyIn (fun (t : ℂ) ↦ f t * g t) (d₁ + d₂) := by
  intro R _ _ f g d₁ d₂ hf hg
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun n => ∑ i ∈ Finset.range (d₁ + 1), ∑ j ∈ Finset.range (d₂ + 1),
    if i + j = n then a i * b j else 0, fun s => ?_⟩
  show f s * g s = _
  rw [ha s, hb s, Finset.sum_mul_sum]
  simp only [Finset.smul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hmem : i + j ∈ Finset.range (d₁ + d₂ + 1) := by
    rw [Finset.mem_range] at hi hj ⊢
    omega
  rw [Finset.sum_eq_single_of_mem (i + j) hmem]
  · rw [if_pos rfl, smul_mul_smul_comm, pow_add]
  · intro k _ hk
    rw [if_neg (Ne.symm hk), smul_zero]
