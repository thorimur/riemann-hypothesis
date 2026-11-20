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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory.ResidueSpanScale

theorem exists_scale {O K J : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite J] (c : J → K) (j : J) (hj : c j ≠ 0) :
    ∃ (j₀ : J) (d : J → O), c j₀ ≠ 0 ∧ d j₀ = 1 ∧ ∀ i, c i = c j₀ * algebraMap O K (d i) := by
  classical
  haveI : Nonempty J := ⟨j⟩
  obtain ⟨j₀, h₀⟩ := Finite.exists_max (fun i => ValuationRing.valuation O K (c i))
  have hv : ValuationRing.valuation O K (c j₀) ≠ 0 := by
    intro h
    have h1 := h₀ j
    rw [h, le_zero_iff] at h1
    exact hj ((Valuation.zero_iff _).1 h1)
  have hc : c j₀ ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hex : ∀ i, ∃ a : O, algebraMap O K a = c i / c j₀ := by
    intro i
    rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (h₀ i) zero_le
  choose d hd using hex
  refine ⟨j₀, d, hc, ?_, fun i => ?_⟩
  · apply IsFractionRing.injective O K
    rw [hd, div_self hc, map_one]
  · rw [hd]; field_simp

theorem finrank_span_residue_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K)
    (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i : I,
      f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O)
        (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  classical
  obtain ⟨κ, e, he, hsp, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField O) g
  haveI : Finite κ := Finite.of_injective e he
  haveI : Fintype κ := Fintype.ofFinite κ
  have hf : LinearIndependent K (f ∘ e) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := hne
    obtain ⟨j₀, d, hc₀, hd₀, hd⟩ := exists_scale (O := O) c j hj
    have hz : ∑ i, IsLocalRing.residue O (d i) • (g ∘ e) i = 0 := by
      funext b
      obtain ⟨a, w, hw⟩ := h b
      have h1 := congrFun hc a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply] at h1 ⊢
      have h2 : c j₀ * algebraMap O K (∑ i, d i * w (e i)) = 0 := by
        rw [← h1, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, (hw (e i)).1, ← mul_assoc, ← hd i]
      have h3 : ∑ i, d i * w (e i) = 0 := by
        apply IsFractionRing.injective O K
        rw [map_zero]
        exact (mul_eq_zero.1 h2).resolve_left hc₀
      have h4 := congrArg (IsLocalRing.residue O) h3
      rw [map_sum, map_zero] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, (hw (e i)).2]
    have := Fintype.linearIndependent_iff.1 hli _ hz j₀
    rw [hd₀, map_one] at this
    exact one_ne_zero this
  haveI : Module.Finite K (Submodule.span K (Set.range f)) :=
    Module.Finite.span_of_finite K (Set.finite_range f)
  rw [← hsp, finrank_span_eq_card hli, ← finrank_span_eq_card hf]
  exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range e f))

end GlobalTheory.ResidueSpanScale
