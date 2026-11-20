import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[reducible] noncomputable def UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conjE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

private theorem UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_eq_neg_of_sq {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ^ 2 = -(r : ℂ)) : starRingEnd ℂ z = -z := by
  have hre : z.re * z.re - z.im * z.im = -r := by
    simpa [pow_two] using congrArg Complex.re hz
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg Complex.im hz
  have hprod : z.re * z.im = 0 := by linarith
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {d : ℕ} {x : E},
      (0 : ℕ) < d → x ^ (2 : ℕ) = -(↑d : E) → (UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conjE E : E → E) x = -x := by
  intro E _ _ _ d x hd hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  change φ (NumberField.IsCMField.complexConj E x) = φ (-x)
  rw [NumberField.IsCMField.complexEmbedding_complexConj, map_neg]
  refine UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_eq_neg_of_sq (r := (d : ℝ)) (Nat.cast_pos.mpr hd) ?_
  rw [← map_pow, hx, map_neg, map_natCast, Complex.ofReal_natCast]
