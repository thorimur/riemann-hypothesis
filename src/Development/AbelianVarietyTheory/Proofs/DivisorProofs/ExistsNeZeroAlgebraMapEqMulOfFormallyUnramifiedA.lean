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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Algebra

namespace GlobalTheory

theorem exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified :
    ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D]
      [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 →
      ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by
  intro P D _ _ _ _ _ _ _ f hf
  by_cases hinj : Function.Injective (algebraMap P D)
  swap
  · rw [injective_iff_map_eq_zero] at hinj
    push_neg at hinj
    obtain ⟨Q, hQ, hQ0⟩ := hinj
    exact ⟨Q, hQ0, 0, by rw [hQ, mul_zero]⟩
  let M := nonZeroDivisors P
  let K := FractionRing P
  let S := Algebra.algebraMapSubmonoid D M
  let L := Localization S
  letI : Algebra K L := localizationAlgebra M D
  haveI : IsScalarTower P K L := inferInstance
  have hS : S ≤ nonZeroDivisors D := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hq))
  haveI : IsDomain L := IsLocalization.isDomain_localization hS
  have hDL : Function.Injective (algebraMap D L) := IsLocalization.injective L hS
  haveI : IsLocalization (M.map (algebraMap P D)) L := inferInstanceAs (IsLocalization S L)
  haveI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.localization_map M (S := D)
  haveI : Algebra.EssFiniteType D L := Algebra.EssFiniteType.of_isLocalization L S
  haveI : Algebra.EssFiniteType P L := Algebra.EssFiniteType.comp P D L
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp P K L
  haveI : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have hint : IsIntegral K (algebraMap D L f) := Algebra.IsIntegral.isIntegral _
  have hne : algebraMap D L f ≠ 0 := (map_ne_zero_iff _ hDL).2 hf
  obtain ⟨u, hu⟩ := hint.isUnit hne
  have hy : algebraMap D L f * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
  obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.surj S (↑u⁻¹ : L)
  obtain ⟨q, hq, hqs⟩ := s.2
  refine ⟨q, nonZeroDivisors.ne_zero hq, d, ?_⟩
  apply hDL
  simp only at hds
  rw [map_mul, ← hds, ← mul_assoc, hy, one_mul, hqs]

end GlobalTheory
