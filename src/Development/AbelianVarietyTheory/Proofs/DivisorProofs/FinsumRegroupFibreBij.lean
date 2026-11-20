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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem finsum_regroup_fibre_bij {α ι : Type} {κ : ι → Type} (U : α → ℂ)
    (W : (i : ι) → κ i → ℂ) (π : α → ι) (Φ : (i : ι) → α → κ i)
    (hU : (Function.support U).Finite)
    (hval : ∀ a, U a ≠ 0 → W (π a) (Φ (π a) a) = U a)
    (hinj : ∀ a a', U a ≠ 0 → U a' ≠ 0 → π a' = π a → Φ (π a) a = Φ (π a) a' → a = a')
    (hsurj : ∀ i c, W i c ≠ 0 → ∃ a, π a = i ∧ U a ≠ 0 ∧ Φ i a = c) :
    ∑ᶠ a, U a = ∑ᶠ i, ∑ᶠ c, W i c := by
  classical
  set S : Finset α := hU.toFinset with hS
  have hmem : ∀ a, a ∈ S ↔ U a ≠ 0 := fun a => by simp [hS]
  have hin : ∀ i, ∑ᶠ c, W i c = ∑ a ∈ S.filter (fun a => π a = i), U a := by
    intro i
    have h1 : Function.support (W i) ⊆
        ((S.filter (fun a => π a = i)).image (Φ i) : Finset (κ i)) := by
      intro c hc
      obtain ⟨a, ha, hUa, hac⟩ := hsurj i c hc
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter]
      exact ⟨a, ⟨(hmem a).2 hUa, ha⟩, hac⟩
    rw [finsum_eq_sum_of_support_subset _ h1, Finset.sum_image]
    · refine Finset.sum_congr rfl fun a ha => ?_
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      subst ha2
      exact hval a ((hmem a).1 ha1)
    · intro a ha a' ha' h
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      obtain ⟨ha1', ha2'⟩ := Finset.mem_filter.1 ha'
      subst ha2
      exact hinj a a' ((hmem a).1 ha1) ((hmem a').1 ha1') ha2' h
  simp only [hin]
  have h2 : Function.support (fun i => ∑ a ∈ S.filter (fun a => π a = i), U a) ⊆
      (S.image π : Finset ι) := by
    intro i hi
    obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨a, ha1, ha2⟩
  rw [finsum_eq_sum_of_support_subset _ h2, finsum_eq_sum U hU,
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem π ha)]

end GlobalTheory
