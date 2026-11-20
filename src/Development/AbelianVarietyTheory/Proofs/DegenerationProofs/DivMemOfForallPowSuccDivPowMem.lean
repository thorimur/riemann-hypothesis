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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Module

namespace GlobalTheory.ZH

theorem div_mem_of_forall_pow_succ_div_pow_mem :
    ∀ (Ω : Type) [Field Ω] (O : Subring Ω) [ValuationRing O] [IsNoetherianRing O],
      (∀ x : Ω, x ∈ O ∨ x⁻¹ ∈ O) → ∀ f f' : Ω, f ≠ 0 → f' ≠ 0 →
        (∀ j : ℕ, 1 ≤ j → f' ^ (j + 1) / f ^ j ∈ O) → f' / f ∈ O := by
  intro Ω _ O _ _ hO f f' hf hf' h
  by_contra hn
  have hg : f / f' ∈ O := by
    rcases hO (f' / f) with h1 | h1
    · exact absurd h1 hn
    · simpa using h1
  set g : O := ⟨f / f', hg⟩ with hgdef
  have hI : Ideal.span {g} ≠ ⊤ := by
    intro htop
    obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_top.mp htop).exists_right_inv
    have hu' : f / f' * (u : Ω) = 1 := congrArg Subtype.val hu
    have : (u : Ω) = f' / f := by
      field_simp at hu' ⊢
      linear_combination hu'
    exact hn (this ▸ u.2)
  have hK := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  have hmem : (⟨f' ^ (1 + 1) / f ^ 1, h 1 le_rfl⟩ : O) ∈ ⨅ n : ℕ, Ideal.span {g} ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨⟨f' ^ (n + 1 + 1) / f ^ (n + 1), h (n + 1) (by omega)⟩, Subtype.ext ?_⟩
    simp only [hgdef, Subring.coe_mul, SubmonoidClass.coe_pow, div_pow]
    field_simp
    ring
  rw [hK, Ideal.mem_bot] at hmem
  have h0 : f' ^ (1 + 1) / f ^ 1 = 0 := congrArg Subtype.val hmem
  exact div_ne_zero (pow_ne_zero _ hf') (pow_ne_zero _ hf) h0

end GlobalTheory.ZH
