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
import Std.Tactic.BVDecide.Normalize.Prop

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem mem_span_indicator_lowerSets :
    ∀ (X L : Type) [Fintype L] [PartialOrder L] (ρ : X → Option L) (Φ : X → ℂ),
      (∀ x, ρ x = none → Φ x = 0) → (∀ x x', ρ x = ρ x' → Φ x = Φ x') →
      Φ ∈ Submodule.span ℂ {Ψ | ∃ l : L, Ψ = Set.indicator {x | ∃ l', ρ x = some l' ∧ l' ≤ l}
        (fun _ => (1 : ℂ))} := by
  classical
  intro X L _ _ ρ Φ h0 hΦ
  set S := Submodule.span ℂ {Ψ : X → ℂ | ∃ l : L, Ψ = Set.indicator
    {x | ∃ l', ρ x = some l' ∧ l' ≤ l} (fun _ => (1 : ℂ))} with hS
  have key : ∀ l : L, Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) ∈ S := by
    intro l
    induction l using WellFoundedLT.induction with
    | ind l ih =>
      have hsum : Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) =
          Set.indicator {x | ∃ l', ρ x = some l' ∧ l' ≤ l} (fun _ => (1 : ℂ)) -
            ∑ l' ∈ Finset.univ.filter (· < l),
              Set.indicator {x | ρ x = some l'} (fun _ => (1 : ℂ)) := by
        funext x
        simp only [Pi.sub_apply, Finset.sum_apply, Set.indicator_apply, Set.mem_setOf_eq]
        cases hx : ρ x with
        | none => simp
        | some m =>
          have h1 : (∃ l', some m = some l' ∧ l' ≤ l) ↔ m ≤ l := by simp
          simp only [Option.some.injEq, h1]
          rw [Finset.sum_ite_eq]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hml : m = l
          · subst hml; simp
          · by_cases hle : m ≤ l
            · have hlt : m < l := lt_of_le_of_ne hle hml
              simp [hml, hle, hlt]
            · have hlt : ¬ m < l := fun h => hle h.le
              simp [hml, hle, hlt]
      rw [hsum]
      exact S.sub_mem (Submodule.subset_span ⟨l, rfl⟩)
        (S.sum_mem fun l' hl' => ih l' (by simpa using hl'))
  let c : L → ℂ := fun l => if h : ∃ x, ρ x = some l then Φ h.choose else 0
  have hdecomp : Φ = ∑ l, c l • Set.indicator {x | ρ x = some l} (fun _ => (1 : ℂ)) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_setOf_eq,
      smul_eq_mul, mul_ite, mul_one, mul_zero]
    cases hx : ρ x with
    | none => simpa using h0 x hx
    | some m =>
      simp only [Option.some.injEq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have hex : ∃ y, ρ y = some m := ⟨x, hx⟩
      simp only [c, dif_pos hex]
      exact hΦ _ _ (hx.trans hex.choose_spec.symm)
  rw [hdecomp]
  exact S.sum_mem fun l _ => S.smul_mem _ (key l)

end GlobalTheory
