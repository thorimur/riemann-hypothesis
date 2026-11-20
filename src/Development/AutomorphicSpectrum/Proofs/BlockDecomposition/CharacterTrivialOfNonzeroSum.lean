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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FiniteQuotientCharacter

theorem eq_one_of_sum_representatives_ne_zero {A : Type} [AddCommGroup A] (T large₂ : AddSubgroup A)
    (R : Finset A) (χ : A → ℂ)
    (hχ : ∀ a ∈ T, ∀ b ∈ T, χ (a + b) = χ a * χ b) (hL : ∀ l ∈ large₂, l ∈ T ∧ χ l = 1)
    (hR : ∀ r ∈ R, r ∈ T) (hU : ∀ m ∈ T, ∃! r, r ∈ R ∧ ∃ l ∈ large₂, m = r + l)
    (hS : (∑ r ∈ R, χ r) ≠ 0) : ∀ m ∈ T, χ m = 1 := by
  classical
  intro m hm
  have hex : ∀ r : A, ∃ s : A, r ∈ R → (s ∈ R ∧ ∃ l ∈ large₂, r + m = s + l) := by
    intro r
    by_cases hr : r ∈ R
    · obtain ⟨s, ⟨hs, hl⟩, -⟩ := hU (r + m) (T.add_mem (hR r hr) hm)
      exact ⟨s, fun _ => ⟨hs, hl⟩⟩
    · exact ⟨r, fun h => absurd h hr⟩
  choose ρ hρ using hex
  have hinj : Set.InjOn ρ (R : Set A) := by
    intro r hr r' hr' h
    obtain ⟨-, l, hl, e⟩ := hρ r hr
    obtain ⟨-, l', hl', e'⟩ := hρ r' hr'
    have hs : ρ r' = r' + m - l' := eq_sub_of_add_eq e'.symm
    rw [h, hs] at e
    apply (hU r (hR r hr)).unique
    · exact ⟨hr, 0, large₂.zero_mem, by simp⟩
    · refine ⟨hr', l - l', large₂.sub_mem hl hl', ?_⟩
      calc r = (r + m) - m := by abel
        _ = r' + (l - l') := by rw [e]; abel
  have hmul : ∀ r ∈ R, χ r * χ m = χ (ρ r) := by
    intro r hr
    obtain ⟨hs, l, hl, e⟩ := hρ r hr
    rw [← hχ r (hR r hr) m hm, e, hχ _ (hR _ hs) l (hL l hl).1, (hL l hl).2, mul_one]
  have himg : R.image ρ = R := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      exact (hρ r hr).1
    · rw [Finset.card_image_of_injOn hinj]
  have hsum : (∑ r ∈ R, χ r) * χ m = ∑ r ∈ R, χ r := by
    rw [Finset.sum_mul, Finset.sum_congr rfl hmul]
    conv_rhs => rw [← himg]
    rw [Finset.sum_image hinj]
  exact mul_left_cancel₀ hS (hsum.trans (mul_one _).symm)

end GlobalTheory.CompanionTheory.FiniteQuotientCharacter
