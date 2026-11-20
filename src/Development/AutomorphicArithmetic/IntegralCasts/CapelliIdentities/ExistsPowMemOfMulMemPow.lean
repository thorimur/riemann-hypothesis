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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Presheaf

theorem UpperTheory.Reformulated.B.Qg1.exists_pow_mem_of_mul_mem_pow :
    ∀ {A : Type} [inst : CommRing A] [IsNoetherianRing A] (m : Ideal A) (δ : A),
    (∀ (a : A), δ * a = (0 : A) → a = (0 : A)) → ∀ (j : ℕ), ∃ (k : ℕ), j ≤ k ∧ ∀ (a : A), δ * a ∈ m ^ k → a ∈ m ^ j := by
  intro A _ _ m δ hδ j
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul m (Ideal.span {δ} : Submodule A A)
  refine ⟨j + c, Nat.le_add_right j c, fun a ha => ?_⟩
  have h1 : δ * a ∈ (m ^ (j + c) • ⊤ ⊓ (Ideal.span {δ} : Submodule A A) : Submodule A A) := by
    refine ⟨?_, Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self δ)⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact ha
  rw [hc (j + c) (Nat.le_add_left c j), Nat.add_sub_cancel] at h1
  have h2 : δ * a ∈ Ideal.span {δ} * m ^ j := by
    rw [mul_comm (Ideal.span {δ}), ← Ideal.smul_eq_mul]
    exact Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨z, hz, hza⟩ := Ideal.mem_span_singleton_mul.mp h2
  have h3 : a - z = 0 := hδ _ (by rw [mul_sub, hza, sub_self])
  rw [sub_eq_zero.mp h3]
  exact hz
