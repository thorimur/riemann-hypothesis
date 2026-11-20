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

theorem finite_away_of_isAlgebraic_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Finite A' B' := by
  intro A B _ _ _ _ hft halg
  obtain ⟨s, hs⟩ := hft.out
  choose y hy hint using fun b : B =>
    (Algebra.IsAlgebraic.isAlgebraic (R := A) b).exists_integral_multiple
  refine ⟨∏ b ∈ s, y b, Finset.prod_ne_zero_iff.mpr fun b _ => hy b, ?_⟩
  intro c A' B' _ _ _ _ _ _ _ _ hA' hB'
  set a := ∏ b ∈ s, y b with ha
  haveI hBB : Algebra.FiniteType B B' :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap A B (a * c))) B'
  haveI : Algebra.FiniteType A B' := Algebra.FiniteType.trans hft hBB
  haveI : Algebra.FiniteType A' B' := .of_restrictScalars_finiteType A A' B'
  have hu : IsUnit (algebraMap A A' (a * c)) := IsLocalization.Away.algebraMap_isUnit (a * c)
  have hunit : ∀ (r : A) (m : ℕ), r ∣ (a * c) ^ m → ∃ r' : A', algebraMap A' B' r' * algebraMap A B' r = 1 := by
    intro r m hr
    obtain ⟨u, hu'⟩ := isUnit_of_dvd_unit (map_dvd (algebraMap A A') hr) (by rw [map_pow]; exact hu.pow m)
    refine ⟨↑u⁻¹, ?_⟩
    rw [IsScalarTower.algebraMap_apply A A' B', ← hu', ← map_mul, Units.inv_mul, map_one]
  haveI : Algebra.IsIntegral A' B' := by
    let S : Subalgebra A B :=
      ((integralClosure A' B').restrictScalars A).comap (IsScalarTower.toAlgHom A B B')
    have hS : Algebra.adjoin A (s : Set B) ≤ S := by
      rw [Algebra.adjoin_le_iff]
      intro b hb
      have h1 : IsIntegral A' (algebraMap B B' (y b • b)) :=
        ((hint b).map (IsScalarTower.toAlgHom A B B')).tower_top
      obtain ⟨r', hr'⟩ := hunit (y b) 1 (by rw [pow_one]; exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hb) c)
      show IsIntegral A' (algebraMap B B' b)
      have : algebraMap B B' b = algebraMap A' B' r' * algebraMap B B' (y b • b) := by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← mul_assoc, hr', one_mul]
      rw [this]
      exact isIntegral_algebraMap.mul h1
    rw [hs] at hS
    constructor
    intro x
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hx⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap A B (a * c))) x
    have hb : IsIntegral A' (algebraMap B B' b) := hS (Algebra.mem_top (x := b))
    obtain ⟨r', hr'⟩ := hunit ((a * c) ^ n) n dvd_rfl
    refine IsIntegral.of_mul_unit (y := algebraMap B B' (algebraMap A B (a * c) ^ n)) (r := r') ?_ ?_
    · rw [← map_pow, ← IsScalarTower.algebraMap_apply]; exact hr'
    · have hx' : x * algebraMap B B' (algebraMap A B (a * c) ^ n) = algebraMap B B' b := hx
      rw [hx']; exact hb
  exact Algebra.IsIntegral.finite

end GlobalTheory
