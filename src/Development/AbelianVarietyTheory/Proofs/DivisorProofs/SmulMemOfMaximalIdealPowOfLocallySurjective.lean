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
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem smul_mem_of_maximalIdeal_pow_of_locally_eq :
    ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup B] [Module R B]
      [Module.Finite R B] (N : Submodule R B),
      (∀ (p : Ideal R), p.IsPrime → p ≠ maximalIdeal R → ∀ b : B, ∃ t ∉ p, t • b ∈ N) →
      ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ N := by
  intro R B _ _ _ _ _ _ N h
  classical
  set J : Ideal R := N.colon (Set.univ : Set B) with hJ
  have hmem : ∀ r : R, r ∈ J ↔ ∀ b : B, r • b ∈ N := by
    intro r
    rw [hJ, Submodule.mem_colon]
    simp
  have hrad : maximalIdeal R ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hJp, hp⟩
    by_cases hpm : p = maximalIdeal R
    · exact hpm.ge
    exfalso
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R B).FG)
    have hg : ∀ g : B, ∃ t ∉ p, t • g ∈ N := h p hp hpm
    choose t ht1 ht2 using hg
    set u : R := ∏ g ∈ s, t g with hu
    have hu_notin : u ∉ p := by
      rw [hu, Ideal.IsPrime.prod_mem_iff]
      rintro ⟨i, -, hi⟩
      exact ht1 i hi
    apply hu_notin
    apply hJp
    rw [hmem]
    intro b
    have hb : b ∈ Submodule.span R (s : Set B) := by rw [hs]; trivial
    have hle : Submodule.span R (s : Set B) ≤ N.comap (u • LinearMap.id) := by
      rw [Submodule.span_le]
      intro g hgs
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hu, ← Finset.prod_erase_mul s t hgs, mul_smul]
      exact N.smul_mem _ (ht2 g)
    have := hle hb
    simpa using this
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (maximalIdeal R))
  exact ⟨k, fun x hx b => (hmem x).1 (hk hx) b⟩

end GlobalTheory
