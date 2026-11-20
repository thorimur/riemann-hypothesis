import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

noncomputable def UpperTheory.Reformulated.B.Qh29.cE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → E ≃+* E :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] ↦ (NumberField.IsCMField.complexConj E).toRingEquiv

theorem UpperTheory.Reformulated.B.Qh29.norm_eq_mul_cE :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K] [inst_2 : NumberField.IsCMField K] (y : K),
      (Algebra.algebraMap (↥(NumberField.maximalRealSubfield K)) K : ↥(NumberField.maximalRealSubfield K) → K)
          ((Algebra.norm ↥(NumberField.maximalRealSubfield K) : K → ↥(NumberField.maximalRealSubfield K)) y) =
        y * (UpperTheory.Reformulated.B.Qh29.cE K : K → K) y := by
  intro K _ _ _ y
  classical
  have hne := NumberField.IsCMField.complexConj_ne_one K
  have hcard : Nat.card (K ≃ₐ[NumberField.maximalRealSubfield K] K) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have huniv : (Finset.univ : Finset (K ≃ₐ[NumberField.maximalRealSubfield K] K)) =
      {1, NumberField.IsCMField.complexConj K} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne.symm, ← Nat.card_eq_fintype_card, hcard]
  have h := Algebra.norm_eq_prod_automorphisms (NumberField.maximalRealSubfield K) y
  rw [huniv, Finset.prod_pair hne.symm] at h
  exact h
