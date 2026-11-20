import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_separating_basicOpen_functions : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  intro X U hU F hFU hsp W hW
  classical
  have key : ∀ a ∈ F, ∃ g : Γ(X, U), a ∈ X.basicOpen g ∧ X.basicOpen g ≤ W a ∧
      ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen g := by
    intro a ha
    let C : Set X := ⋃ b ∈ F.erase a, closure {b}
    have hC : IsClosed C := isClosed_biUnion_finset (fun b _ => isClosed_closure)
    let V : X.Opens := W a ⊓ ⟨Cᶜ, hC.isOpen_compl⟩
    have haC : a ∉ C := by
      simp only [C, Set.mem_iUnion, not_exists]
      intro b hb hab
      have hb' := Finset.mem_erase.mp hb
      exact hb'.1 (hsp b hb'.2 a ha (specializes_iff_mem_closure.mpr hab))
    have haV : a ∈ V := ⟨hW a ha, haC⟩
    obtain ⟨g, hgV, hag⟩ := hU.exists_basicOpen_le ⟨a, haV⟩ (hFU a ha)
    refine ⟨g, hag, le_trans hgV inf_le_left, ?_⟩
    intro b hb hba hbg
    have hbV : b ∈ V := hgV hbg
    apply hbV.2
    simp only [C, Set.mem_iUnion]
    exact ⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩, subset_closure rfl⟩
  choose! f hf using key
  exact ⟨f, hf⟩

end GlobalTheory
