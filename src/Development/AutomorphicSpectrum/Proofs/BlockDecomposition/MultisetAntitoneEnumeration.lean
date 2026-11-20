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
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory.CompanionTheory.Multiset

theorem exists_antitone_listing {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop)
    (hP : ∀ a b, P a b → f a < f b) :
    ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧
      ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  classical
  obtain ⟨l, rfl⟩ := Quot.exists_rep m
  let r : α → α → Prop := fun a b => f b ≤ f a
  haveI : DecidableRel r := fun _ _ => Classical.dec _
  haveI : IsTotal α r := ⟨fun a b => le_total (f b) (f a)⟩
  haveI : IsTrans α r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  let l' := l.insertionSort r
  have hperm : l'.Perm l := List.perm_insertionSort r l
  have hsort : l'.Pairwise r := List.pairwise_insertionSort r l
  have hlt : ∀ i j : Fin l'.length, i < j → f (l'.get j) ≤ f (l'.get i) := by
    intro i j hij
    exact (List.pairwise_iff_get.mp hsort) i j hij
  refine ⟨l'.length, l'.get, ?_, ?_, ?_⟩
  · have h1 : (Finset.univ : Finset (Fin l'.length)).val.map l'.get = ((List.ofFn l'.get : List α) : Multiset α) := by
      rw [Fin.univ_val_map]
    rw [h1, List.ofFn_get]
    exact Quot.sound hperm
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact hlt i j h
    · subst h; exact le_rfl
  · intro i j hij hp
    exact absurd (hP _ _ hp) (not_lt.mpr (hlt i j hij))

end GlobalTheory.CompanionTheory.Multiset
