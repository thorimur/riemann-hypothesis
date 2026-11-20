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

private lemma sum_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hs : Summable g) (s : Finset (ι → α)) :
    ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∏ _i : ι, ∑' x, g x := by
  haveI : DecidableEq α := Classical.decEq α
  let t : ι → Finset α := fun i => s.image fun η : ι → α => η i
  have hsub : s ⊆ Fintype.piFinset t := by
    intro ξ hξ
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.2 ⟨ξ, hξ, rfl⟩
  have h1 : ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun ξ _ _ => Finset.prod_nonneg fun i _ => hg (ξ i)
  have h2 : ∏ i, ∑ x ∈ t i, g x = ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.prod_univ_sum t fun _ x => g x
  have h3 : ∏ i, ∑ x ∈ t i, g x ≤ ∏ _i : ι, ∑' x, g x := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg fun x _ => hg x
    · intro i _
      exact hs.sum_le_tsum (t i) fun x _ => hg x
  exact h1.trans (h2.symm.le.trans h3)

theorem UpperTheory.Reformulated.B.Qo1.summable_prod_coord.{u_2, u_3} :
    ∀ {ι : Type u_2} [inst : Fintype ι] [DecidableEq ι] {α : Type u_3} {g : α → ℝ},
    (∀ (x : α), (0 : ℝ) ≤ g x) → Summable g → Summable fun (ξ : ι → α) ↦ ∏ i : ι, g (ξ i) := by
  intro ι _ _ α g hg hs
  have h0 : ∀ ξ : ι → α, 0 ≤ ∏ i, g (ξ i) := fun ξ => Finset.prod_nonneg fun i _ => hg (ξ i)
  exact summable_of_sum_le h0 (sum_prod_le hg hs)
