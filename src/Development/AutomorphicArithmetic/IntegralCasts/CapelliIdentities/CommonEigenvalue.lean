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
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf

theorem UpperTheory.Reformulated.B.CommonEigenvectorOfCommutingSet.common_eig :
    ∀ {k : Type} [inst : Field k] [IsAlgClosed k]
    {V : Type} [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V] [FiniteDimensional k V] (S : Set (Module.End k V)),
    (∀ f ∈ S, ∀ f' ∈ S, f * f' = f' * f) →
      ∀ (d : ℕ) (W : Submodule k V),
        Module.finrank k ↥W = d →
          W ≠ ⊥ →
            (∀ f ∈ S, ∀ x ∈ W, (f : V → V) x ∈ W) → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ f ∈ S, ∃ (c : k), (f : V → V) v = c • v := by
  intro k _ _ V _ _ _ S hS d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro W hd hW hinv
    by_cases h : ∀ f ∈ S, ∀ x ∈ W, ∃ c : k, f x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨v, hv, hv0, fun f hf => h f hf v hv⟩
    · push Not at h
      obtain ⟨f, hf, x, hx, hfx⟩ := h
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict (hinv f hf) : Module.End k W)
      obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
      have hwe : f (w : V) = μ • (w : V) := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [LinearMap.restrict_apply] using h1
      have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : W ⊓ f.eigenspace μ < W := by
        refine lt_of_le_of_ne inf_le_left fun he => ?_
        have hx' : x ∈ W ⊓ f.eigenspace μ := he.symm ▸ hx
        exact hfx μ (Module.End.mem_eigenspace_iff.mp hx'.2)
      have hne : W ⊓ f.eigenspace μ ≠ ⊥ := by
        intro hb
        have hm : (w : V) ∈ W ⊓ f.eigenspace μ :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hwe⟩
        rw [hb] at hm
        exact hw0 ((Submodule.mem_bot k).mp hm)
      have hinv' : ∀ g ∈ S, ∀ y ∈ W ⊓ f.eigenspace μ, g y ∈ W ⊓ f.eigenspace μ := by
        intro g hg y hy
        refine ⟨hinv g hg y hy.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 : f y = μ • y := Module.End.mem_eigenspace_iff.mp hy.2
        have h2 : f (g y) = g (f y) := LinearMap.congr_fun (hS f hf g hg) y
        rw [h2, h1, map_smul]
      obtain ⟨v, hv, hv0, hv'⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hinv'
      exact ⟨v, hv.1, hv0, hv'⟩
