import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
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

namespace GlobalTheory

theorem dvd_of_associated_at_height_one (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (a b : A) (hb : b ≠ 0)
    (h : ∀ (q : Ideal A) [q.IsPrime], q.height = 1 →
      Associated (algebraMap A (Localization.AtPrime q) a)
        (algebraMap A (Localization.AtPrime q) b)) : b ∣ a := by
  let K := FractionRing A
  have hbK : algebraMap A K b ≠ 0 := fun h0 =>
    hb (IsFractionRing.injective A K (by rw [h0, map_zero]))
  have hmem : algebraMap A K a / algebraMap A K b ∈ (algebraMap A K).range := by
    refine ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := A) _ ?_
    intro P hP h1
    obtain ⟨u, hu⟩ := h P h1
    obtain ⟨c, s, hcs⟩ := IsLocalization.exists_mk'_eq P.primeCompl
      (((u⁻¹ : (Localization.AtPrime P)ˣ)) : Localization.AtPrime P)
    have h2 : algebraMap A (Localization.AtPrime P) a =
        algebraMap A (Localization.AtPrime P) b * IsLocalization.mk' _ c s := by
      rw [hcs, ← hu, mul_assoc, Units.mul_inv, mul_one]
    have h3 : algebraMap A (Localization.AtPrime P) (a * s) =
        algebraMap A (Localization.AtPrime P) (b * c) := by
      rw [map_mul, h2, mul_assoc, IsLocalization.mk'_spec, map_mul]
    have e : a * s = b * c :=
      IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors h3
    refine ⟨s, s.2, c, ?_⟩
    have e' : algebraMap A K a * algebraMap A K s = algebraMap A K b * algebraMap A K c := by
      rw [← map_mul, ← map_mul, e]
    rw [← mul_div_assoc, eq_div_iff hbK]
    linear_combination -e'
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hc, mul_div_assoc', eq_div_iff hbK, mul_comm]

theorem associated_of_associated_at_height_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (a b : A),
      a ≠ 0 → b ≠ 0 →
      (∀ (q : Ideal A) [q.IsPrime], q.height = 1 →
        Associated (algebraMap A (Localization.AtPrime q) a)
          (algebraMap A (Localization.AtPrime q) b)) →
      Associated a b := by
  intro A _ _ _ _ a b ha hb h
  refine associated_of_dvd_dvd ?_ ?_
  · exact dvd_of_associated_at_height_one A b a ha (fun q _ h1 => (h q h1).symm)
  · exact dvd_of_associated_at_height_one A a b hb h

end GlobalTheory
