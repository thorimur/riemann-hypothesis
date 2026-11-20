import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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

open CategoryTheory

namespace GlobalTheory

theorem exists_compatible_seq_of_finite_nonempty
    (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n))
    (hfin : ∀ n, (Y n).Finite) (hne : ∀ n, (Y n).Nonempty)
    (hmap : ∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) :
    ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  classical
  let g : ∀ n, ((Y (n + 1) : Set (X (n + 1))) : Type) ⟶ ((Y n : Set (X n)) : Type) :=
    fun n => TypeCat.ofHom (fun x => ⟨f n x.1, hmap n x.1 x.2⟩)
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun n => ((Y n : Set (X n)) : Type)) g
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => (u (Opposite.op n)).1, fun n => ⟨(u (Opposite.op n)).2, ?_⟩⟩
  have h := hu (homOfLE (Nat.le_add_right n 1)).op
  have hm : F.map (homOfLE (Nat.le_add_right n 1)).op = g n :=
    Functor.ofOpSequence_map_homOfLE_succ (X := fun n => ((Y n : Set (X n)) : Type)) g n
  rw [hm] at h
  exact congrArg Subtype.val h

end GlobalTheory
