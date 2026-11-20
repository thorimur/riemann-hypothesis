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
import Mathlib.Order.CompletePartialOrder
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

theorem finsum_fiberwise_of_finite_support {A B : Type} (ρ : A → B) (f : A → ℂ)
    (hf : (Function.support f).Finite) :
    ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by
  classical
  set S := hf.toFinset with hS
  have hsupp : Function.support f ⊆ (S : Set A) := by simp [hS]
  have hinner : ∀ b, (∑ᶠ a : {a // ρ a = b}, f a.1) = ∑ a ∈ S with ρ a = b, f a := by
    intro b
    rw [finsum_subtype_eq_finsum_cond (fun a => ρ a = b)]
    have : (fun a => ∑ᶠ (_ : ρ a = b), f a) = fun a => if ρ a = b then f a else 0 := by
      funext a; exact finsum_eq_if
    rw [this, finsum_eq_sum_of_support_subset _ (s := S), Finset.sum_filter]
    intro a ha
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at ha
    obtain ⟨_, h⟩ := ha
    exact hsupp h
  simp_rw [hinner]
  rw [finsum_eq_sum_of_support_subset f hsupp,
    finsum_eq_sum_of_support_subset _ (s := S.image ρ)]
  · exact (Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem ρ ha) f).symm
  · intro b hb
    rw [Function.mem_support] at hb
    obtain ⟨a, ha, hab⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    rw [Finset.mem_filter] at ha
    rw [Finset.coe_image]
    exact ⟨a, ha.1, ha.2⟩

end GlobalTheory
