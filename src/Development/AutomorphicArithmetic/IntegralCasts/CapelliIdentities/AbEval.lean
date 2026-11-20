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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

theorem UpperTheory.Reformulated.B.Ra1.ab_eval :
    ∀ {k X : Type} [inst : Field k] [Inhabited X] (r : ℕ)
    (H : Submodule k (X → k)),
    Module.Finite k ↥H →
      Module.finrank k ↥H ≤ r → ∃ (t : Fin r → X), ∀ φ ∈ H, (∀ (a : Fin r), φ (t a) = (0 : k)) → φ = (0 : X → k) := by
  intro k X inst _ r
  induction r with
  | zero =>
    intro H hfin hr
    have hH : H = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hr)
    refine ⟨fun _ => default, fun φ hφ _ => ?_⟩
    rw [hH] at hφ
    exact (Submodule.mem_bot k).mp hφ
  | succ n ih =>
    intro H hfin hr
    by_cases h : ∀ φ ∈ H, φ = 0
    · exact ⟨fun _ => default, fun φ hφ _ => h φ hφ⟩
    · have h' : ∃ ψ ∈ H, ∃ x, ψ x ≠ 0 := by
        by_contra hc
        apply h
        intro φ hφ
        funext x
        by_contra hx
        exact hc ⟨φ, hφ, x, hx⟩
      obtain ⟨ψ, hψ, x, hx⟩ := h'
      let K : Submodule k (X → k) :=
        H ⊓ LinearMap.ker (LinearMap.proj (R := k) (φ := fun _ : X => k) x)
      have hle : K ≤ H := inf_le_left
      have hlt : K < H := by
        refine lt_of_le_of_ne hle ?_
        intro he
        have hK : ψ ∈ K := he ▸ hψ
        exact hx hK.2
      have hKfin : Module.Finite k ↥K := Submodule.finiteDimensional_of_le hle
      have hrank : Module.finrank k ↥K < Module.finrank k ↥H :=
        Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨t, ht⟩ := ih K hKfin (by omega)
      refine ⟨Fin.cons x t, fun φ hφ h0 => ?_⟩
      exact ht φ ⟨hφ, h0 0⟩ (fun a => h0 a.succ)
