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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Presheaf
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.HermitianCommuting

theorem exists_maximal_commuting_hermitian_subspace {n : ℕ}
    (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧
      (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  let S : Set (Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
    {a | a ≤ 𝔤 ∧ (∀ A ∈ a, Aᴴ = A) ∧ ∀ A ∈ a, ∀ B ∈ a, A * B = B * A}
  have hS : S.Nonempty := by
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · intro A hA
      rw [Submodule.mem_bot] at hA
      simp [hA]
    · intro A hA B hB
      rw [Submodule.mem_bot] at hA hB
      simp [hA, hB]
  obtain ⟨a, ha, hmax⟩ :=
    (wellFounded_gt (α := Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).has_min S hS
  refine ⟨a, ha.1, ha.2.1, ha.2.2, ?_⟩
  intro Y hY hYh hYc
  have hmem : a ⊔ Submodule.span ℝ {Y} ∈ S := by
    refine ⟨sup_le ha.1 ((Submodule.span_singleton_le_iff_mem _ _).2 hY), ?_, ?_⟩
    · intro A hA
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [conjTranspose_add, ha.2.1 x hx, conjTranspose_smul, hYh]
      simp
    · intro A hA B hB
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.1 hB
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      have h1 := ha.2.2 x hx x' hx'
      have h2 := hYc x hx
      have h3 := hYc x' hx'
      simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h1, h2, h3]
      rw [mul_comm d c]
      abel
  have hne : a ⊔ Submodule.span ℝ {Y} = a := by
    by_contra h
    exact hmax _ hmem (lt_of_le_of_ne le_sup_left (Ne.symm h))
  have hYmem : Y ∈ a ⊔ Submodule.span ℝ {Y} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self Y)
  rwa [hne] at hYmem

end GlobalTheory.CompanionTheory.HermitianCommuting
