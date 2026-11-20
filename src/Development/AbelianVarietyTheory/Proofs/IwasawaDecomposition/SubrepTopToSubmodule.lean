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
import Mathlib.RepresentationTheory.Irreducible
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

namespace GlobalTheory.SubrepTopBot

open Representation

theorem subrep_bot_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

theorem subrep_top_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

theorem main : ∀ {G : Type} [inst : Group G] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro G _ V _ _ ρ
  have hbot := subrep_bot_toSubmodule ρ
  have htop := subrep_top_toSubmodule ρ
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
      rw [← Submodule.nontrivial_iff ℂ]
      refine ⟨⟨⊥, ⊤, fun e => hne ?_⟩⟩
      apply Subrepresentation.toSubmodule_injective
      rw [hbot, htop]; exact e
    · intro U hU
      let S : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
      rcases h.eq_bot_or_eq_top S with e | e
      · left
        have := congrArg Subrepresentation.toSubmodule e
        rw [hbot] at this; exact this
      · right
        have := congrArg Subrepresentation.toSubmodule e
        rw [htop] at this; exact this
  · rintro ⟨hV, hU⟩
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun e => ?_⟩⟩
      have := congrArg Subrepresentation.toSubmodule e
      rw [hbot, htop] at this
      exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this
    refine { eq_bot_or_eq_top := ?_ }
    intro S
    rcases hU S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · left; apply Subrepresentation.toSubmodule_injective; rw [hbot]; exact e
    · right; apply Subrepresentation.toSubmodule_injective; rw [htop]; exact e

end GlobalTheory.SubrepTopBot
