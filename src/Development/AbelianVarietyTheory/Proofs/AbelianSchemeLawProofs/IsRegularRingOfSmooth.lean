import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Unramified.LocalStructure
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem isRegularLocalRing_atPrime_of_etale' (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime]
    (h : IsRegularLocalRing (Localization.AtPrime (q.under R))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have hlo : q.LiesOver (q.under R) := ⟨rfl⟩
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hmax : (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R (q.under R) q).mp inferInstance).2
  have hsf : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank := by
    have heq : IsLocalRing.maximalIdeal (Localization.AtPrime q) =
        (IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) := by
      rw [← hmax, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq]
    rw [heq]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsLocalRing.maximalIdeal _).fg_of_isNoetherianRing
  have hht : (q.under R).height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (q.under R) q]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((IsLocalRing.maximalIdeal (Localization.AtPrime (q.under R))).spanFinrank : WithBot ℕ∞) := by
        exact_mod_cast hsf
    _ = ringKrullDim (Localization.AtPrime (q.under R)) := h.spanFinrank_maximalIdeal
    _ = ((q.under R).height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (q.under R) _
    _ ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ = ringKrullDim (Localization.AtPrime q) :=
        (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm

theorem isRegularRing_of_etale (R S : Type*) [CommRing R] [IsRegularRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  exact isRegularRing_iff.mpr fun q _ => isRegularLocalRing_atPrime_of_etale' R S q inferInstance

theorem isRegularRing_of_smooth :
    ∀ (V B : Type) [CommRing V] [IsRegularRing V] [CommRing B] [Algebra V B] [Algebra.Smooth V B],
      IsRegularRing B := by
  intro V B _ _ _ _ _
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing V B
  refine isRegularRing_iff.mpr fun Q _ => ?_
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := V) (p := Q)
  have hT : IsRegularRing (Localization.Away f) :=
    isRegularRing_of_etale (MvPolynomial (Fin n) V) (Localization.Away f)
  have disj : Disjoint (Submonoid.powers f : Set B) (Q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let Q' := Q.map (algebraMap B (Localization.Away f))
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime Q') Q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f)
      (Localization.AtPrime Q') Q'
    exact (IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› disj).symm
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q') (Localization.AtPrime Q)).toRingEquiv

end GlobalTheory
