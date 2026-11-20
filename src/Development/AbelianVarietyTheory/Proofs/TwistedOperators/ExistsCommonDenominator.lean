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
import Mathlib.RingTheory.PiTensorProduct
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

namespace GlobalTheory.CommonDenominatorLemma

open NumberField

theorem exists_common_denominator {E : Type} [inst : Field E] [NumberField E] [StarRing E] {N : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) (hL : Submodule.FG L) :
    ∃ (b : NumberField.RingOfIntegers E), b ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∀ x ∈ L, ∀ (i : Fin N), ∃ (u : NumberField.RingOfIntegers E), (↑u : E) = (↑b : E) * x i := by
  obtain ⟨s, rfl⟩ := hL
  choose z hz using fun p : (Fin N → E) × Fin N =>
    IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) (p.1 p.2)
  let b : NumberField.RingOfIntegers E :=
    ∏ p ∈ s ×ˢ (Finset.univ : Finset (Fin N)), ((z p).2 : NumberField.RingOfIntegers E)
  refine ⟨b, Finset.prod_ne_zero_iff.mpr fun p _ => nonZeroDivisors.ne_zero (z p).2.2, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem (fun p => ((z p).2 : NumberField.RingOfIntegers E))
      (show (g, i) ∈ s ×ˢ (Finset.univ : Finset (Fin N)) from
        Finset.mem_product.mpr ⟨hg, Finset.mem_univ i⟩)
    refine ⟨e * (z (g, i)).1, ?_⟩
    have h := hz (g, i)
    simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap] at h
    rw [show b = ((z (g, i)).2 : NumberField.RingOfIntegers E) * e from he]
    push_cast
    linear_combination (-(e : E)) * h
  | zero =>
    intro i
    exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    obtain ⟨c2, h2⟩ := hy i
    refine ⟨c1 + c2, ?_⟩
    rw [Pi.add_apply, mul_add, ← h1, ← h2]
    push_cast
    ring
  | smul t x _ hx =>
    intro i
    obtain ⟨c1, h1⟩ := hx i
    refine ⟨t * c1, ?_⟩
    rw [Pi.smul_apply, Algebra.smul_def, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    push_cast
    linear_combination (t : E) * h1

end GlobalTheory.CommonDenominatorLemma
