import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def integralAtPlaces {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) :
    Subalgebra ℤ L where
  carrier := {x | ∀ w ∈ S, w x ≤ 1}
  mul_mem' {a b} ha hb w hw := by
    rw [map_mul]
    exact mul_le_one₀ (ha w hw) (apply_nonneg w b) (hb w hw)
  add_mem' {a b} ha hb w hw := (FinitePlace.add_le w a b).trans (max_le (ha w hw) (hb w hw))
  algebraMap_mem' z w _ := by
    rw [eq_intCast, ← FinitePlace.mk_maximalIdeal w, FinitePlace.mk_apply,
      FinitePlace.norm_embedding]
    exact NumberField.HeightOneSpectrum.adicAbv_intCast_le_one (K := L) (v := w.maximalIdeal) z

def SemilocalQuotCard.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (S : Set (FinitePlace L)), S.Finite →
    ∀ t : integralAtPlaces S, t ≠ 0 →
      (Nat.card (integralAtPlaces S ⧸ Ideal.span {t}) : ℝ) = ∏ᶠ w ∈ S, (w (t : L))⁻¹

example : ∃ (S : Set (FinitePlace ℚ)) (t : integralAtPlaces S), S.Finite ∧ S.Nonempty ∧ t ≠ 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 ℚ)
  have hne : P ≠ ⊥ := fun h ↦
    RingOfIntegers.not_isField ℚ (Ring.isField_iff_maximal_bot.mpr (h ▸ hP))
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := ⟨P, hP.isPrime, hne⟩
  refine ⟨{FinitePlace.mk v}, 2, Set.finite_singleton _, Set.singleton_nonempty _, ?_⟩
  intro h
  have := congrArg (fun y : integralAtPlaces ({FinitePlace.mk v} : Set (FinitePlace ℚ)) ↦ (y : ℚ)) h
  norm_num at this

end GroundTheory.Heights₂.Heights
