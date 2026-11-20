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

theorem UpperTheory.Reformulated.B.Ra6.irr_iff :
    ∀ {G W : Type} [inst : Group G] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module ℂ W] (ρ : Representation ℂ G W),
    ρ.IsIrreducible ↔
      Nontrivial W ∧
        ∀ (N : Submodule ℂ W), (∀ (g : G), ∀ v ∈ N, ((ρ : G → W →ₗ[ℂ] W) g : W → W) v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro G W _ _ _ ρ
  constructor
  · intro h
    have h' : IsSimpleOrder (Subrepresentation ρ) := h
    refine ⟨?_, fun N hN => ?_⟩
    · have hne : (⊥ : Submodule ℂ W) ≠ ⊤ := fun e =>
        (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
      exact (Submodule.nontrivial_iff ℂ).mp ⟨⊥, ⊤, hne⟩
    · rcases h'.eq_bot_or_eq_top ⟨N, fun g v hv => hN g v hv⟩ with e | e
      · exact Or.inl (congrArg Subrepresentation.toSubmodule e)
      · exact Or.inr (congrArg Subrepresentation.toSubmodule e)
  · rintro ⟨hW, h⟩
    have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun e =>
      (bot_ne_top (α := Submodule ℂ W)) (congrArg Subrepresentation.toSubmodule e)
    have h' : IsSimpleOrder (Subrepresentation ρ) :=
      { exists_pair_ne := ⟨⊥, ⊤, hne⟩
        eq_bot_or_eq_top := fun σ =>
          (h σ.toSubmodule fun g v hv => σ.apply_mem_toSubmodule g hv).imp
            (fun e => Subrepresentation.toSubmodule_injective e)
            (fun e => Subrepresentation.toSubmodule_injective e) }
    exact h'
