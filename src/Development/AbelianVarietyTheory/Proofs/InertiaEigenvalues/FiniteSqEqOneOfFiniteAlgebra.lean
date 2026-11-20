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
import Mathlib.RingTheory.PicardGroup
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

namespace GlobalTheory

theorem finite_sq_eq_one_of_finite_algebra (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A]
    [Algebra k A] [Module.Finite k A] : Set.Finite {x : A | x ^ 2 = 1} := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Finite (TopologicalSpace.Clopens (PrimeSpectrum A)) :=
    Finite.of_injective (fun s : TopologicalSpace.Clopens (PrimeSpectrum A) => (s : Set (PrimeSpectrum A)))
      SetLike.coe_injective
  haveI : Finite {e : A // IsIdempotentElem e} :=
    Finite.of_equiv _ (PrimeSpectrum.isIdempotentElemEquivClopens (R := A)).symm.toEquiv
  set c : A := algebraMap k A (2⁻¹ : k) with hc
  have hc2 : c * 2 = 1 := by
    rw [hc, (map_ofNat (algebraMap k A) 2).symm, ← map_mul,
      inv_mul_cancel₀ (two_ne_zero : (2 : k) ≠ 0), map_one]
  have hmap : ∀ x : A, x ^ 2 = 1 → IsIdempotentElem (c * (1 + x)) := by
    intro x hx
    unfold IsIdempotentElem
    have : (c * (1 + x)) * (c * (1 + x)) = c * (c * 2) * (1 + x) := by
      linear_combination (c * c) * hx
    rw [this, hc2, mul_one]
  have hinj : Set.InjOn (fun x : A => c * (1 + x)) {x : A | x ^ 2 = 1} := by
    intro x _ y _ hxy
    have h : (2 : A) * (c * (1 + x)) = 2 * (c * (1 + y)) := by simp only at hxy; rw [hxy]
    have e : ∀ z : A, (2 : A) * (c * (1 + z)) = 1 + z := fun z => by
      rw [← mul_assoc, mul_comm (2 : A) c, hc2, one_mul]
    rw [e, e] at h
    exact add_left_cancel h
  have hfin : Set.Finite {e : A | IsIdempotentElem e} :=
    Set.finite_coe_iff.mp (‹Finite {e : A // IsIdempotentElem e}› :)
  exact Set.Finite.of_finite_image (hfin.subset (by
    rintro _ ⟨x, hx, rfl⟩; exact hmap x hx)) hinj

end GlobalTheory
