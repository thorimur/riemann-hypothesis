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
import Mathlib.RingTheory.Valuation.LocalSubring
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

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd

theorem exists_val_of_prime {Kf : Type*} [Field Kf] (A : Subring Kf) (P : Ideal A) [P.IsPrime] :
    ∃ V : ValuationSubring Kf, (∀ a : A, (a : Kf) ∈ V) ∧ (∀ a : A, a ∉ P → (a : Kf)⁻¹ ∈ V) ∧
      ∀ a : A, a ∈ P → V.valuation (a : Kf) < 1 := by
  obtain ⟨B, hB⟩ := (LocalSubring.ofPrime A P).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hB
  let e := LocalSubring.ofPrimeEquiv A P
  let f : Localization.AtPrime P →+* B.toLocalSubring.toSubring :=
    (Subring.inclusion hle).comp (e : Localization.AtPrime P →+* (LocalSubring.ofPrime A P).toSubring)
  have hf : ∀ a : A, ((f (algebraMap A (Localization.AtPrime P) a) : B.toLocalSubring.toSubring) : Kf) = a := by
    intro a
    show ((e (algebraMap A (Localization.AtPrime P) a) : (LocalSubring.ofPrime A P).toSubring) : Kf) = a
    rw [AlgEquiv.commutes]
    rfl
  have hmem : ∀ a : A, (a : Kf) ∈ B := by
    intro a
    have h := (f (algebraMap A (Localization.AtPrime P) a)).2
    rw [hf] at h
    exact h
  refine ⟨B, hmem, fun a ha => ?_, fun a ha => ?_⟩
  · have hu : IsUnit (algebraMap A (Localization.AtPrime P) a) :=
      IsLocalization.map_units _ (⟨a, ha⟩ : P.primeCompl)
    obtain ⟨u, hu'⟩ := hu.map f
    have h1 : ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) * (u : _) = 1 :=
      u.inv_mul
    have h2 : (((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring) : Kf) * (a : Kf) = 1 := by
      rw [← hf a, ← hu']
      exact congrArg Subtype.val h1
    rw [← eq_inv_of_mul_eq_one_left h2]
    exact ((u⁻¹ : (B.toLocalSubring.toSubring)ˣ) : B.toLocalSubring.toSubring).2
  · have hnu : ¬ IsUnit (algebraMap A (Localization.AtPrime P) a) := fun h =>
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).1 h ha
    have hnu2 : ¬ IsUnit (f (algebraMap A (Localization.AtPrime P) a)) := by
      intro h
      apply hnu
      have h' : IsUnit (e (algebraMap A (Localization.AtPrime P) a)) := hloc.map_nonunit _ h
      have h'' := h'.map (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
      first
      | (convert h'' using 1
         exact (e.symm_apply_apply _).symm)
      | (rwa [show (e.symm : (LocalSubring.ofPrime A P).toSubring →+* Localization.AtPrime P)
            (e (algebraMap A (Localization.AtPrime P) a)) = algebraMap A (Localization.AtPrime P) a from
            e.symm_apply_apply _] at h'')
    by_contra hge
    push_neg at hge
    have hv1 : B.valuation (a : Kf) = 1 := le_antisymm ((B.valuation_le_one_iff _).2 (hmem a)) hge
    have hunit : IsUnit (⟨a, hmem a⟩ : B) := (B.valuation_eq_one_iff ⟨a, hmem a⟩).2 hv1
    apply hnu2
    have heq : f (algebraMap A (Localization.AtPrime P) a) = ⟨a, hmem a⟩ := Subtype.ext (hf a)
    rw [heq]
    exact hunit

end ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd
