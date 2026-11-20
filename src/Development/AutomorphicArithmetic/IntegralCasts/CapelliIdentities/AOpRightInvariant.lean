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

noncomputable def UpperTheory.Reformulated.B.Qf37.aOp :
    {G : Type} → [Group G] → Finset G → G → (G → ℂ) → G → ℂ :=
    fun {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) (g : G) ↦ ∑ r ∈ R, φ (g * r * t)

theorem UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant :
    ∀ {G : Type} [inst : Group G] {I : Subgroup G} {t : G} {R : Finset G},
      (∀ r ∈ R, r ∈ I) →
        (∀ i ∈ I, ∃! r : G, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) →
          ∀ {φ : G → ℂ},
            (∀ (g i : G), i ∈ I → φ (g * i) = φ g) →
              ∀ (g i : G), i ∈ I → UpperTheory.Reformulated.B.Qf37.aOp R t φ (g * i) = UpperTheory.Reformulated.B.Qf37.aOp R t φ g := by
  intro G inst I t R hR hU φ hφ g i hi
  have hex : ∀ r ∈ R, ∃ s, s ∈ R ∧ t⁻¹ * (s⁻¹ * (i * r)) * t ∈ I := fun r hr =>
    (hU (i * r) (I.mul_mem hi (hR r hr))).exists
  choose σ hσR hσ using hex
  have hinj : ∀ a (ha : a ∈ R) b (hb : b ∈ R), σ a ha = σ b hb → a = b := by
    intro a ha b hb hab
    have h1 := hσ a ha
    have h2 := hσ b hb
    rw [← hab] at h2
    have h3 := I.mul_mem (I.inv_mem h1) h2
    have h4 : t⁻¹ * (a⁻¹ * b) * t ∈ I := by
      convert h3 using 1
      group
    have h5 : t⁻¹ * (b⁻¹ * b) * t ∈ I := by
      simp
    exact (hU b (hR b hb)).unique ⟨ha, h4⟩ ⟨hb, h5⟩
  unfold UpperTheory.Reformulated.B.Qf37.aOp
  refine Finset.sum_bij σ hσR hinj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le σ hσR
      (fun a b ha hb h => hinj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, hab.symm⟩
  · intro a ha
    rw [← hφ (g * σ a ha * t) _ (hσ a ha)]
    congr 1
    group
