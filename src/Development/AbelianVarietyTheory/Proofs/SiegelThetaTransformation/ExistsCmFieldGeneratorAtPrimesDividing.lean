import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Presheaf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem exists_span_eq_mul_coprime {R : Type*} [CommRing R] [IsDedekindDomain R]
    (J K : Ideal R) (hJ : J ≠ ⊥) (hK : K ≠ ⊥) :
    ∃ (a : R) (A : Ideal R), a ≠ 0 ∧ Ideal.span {a} = J * A ∧ IsCoprime A K := by
  classical
  have hJK : J * K ≠ ⊥ := mul_ne_zero hJ hK

  obtain ⟨a₀, ha₀⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.mul_le_inf.trans inf_le_left : J * K ≤ J) hJK
  obtain ⟨b, hbJK, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJK

  have key : ∃ a : R, a ≠ 0 ∧ J * K ⊔ Ideal.span {a} = J := by
    by_cases h0 : a₀ = 0
    · refine ⟨b, hb0, ?_⟩
      have hJKJ : J * K = J := by simpa [h0] using ha₀
      rw [sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJK)), hJKJ]
    · exact ⟨a₀, h0, ha₀⟩
  obtain ⟨a, ha0, ha⟩ := key
  have haJ : Ideal.span {a} ≤ J := ha ▸ le_sup_right
  obtain ⟨A, hA⟩ := Ideal.dvd_iff_le.mpr haJ
  refine ⟨a, A, ha0, hA, ?_⟩
  rw [Ideal.isCoprime_iff_sup_eq]

  have h1 : J * (K ⊔ A) = J * ⊤ := by
    rw [Ideal.mul_sup, ← hA, ha, Ideal.mul_top]
  rw [sup_comm]
  exact mul_left_cancel₀ hJ h1

theorem exists_generator_at_primes_dividing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔍 : Ideal (𝓞 E)) (M : ℕ), 𝔍 ≠ ⊥ → 0 < M → ∃ (α : 𝓞 E) (𝔞 : Ideal (𝓞 E)), α ≠ 0 ∧ Ideal.span {α} = 𝔍 * 𝔞 ∧ IsCoprime 𝔞 (Ideal.span {(M : 𝓞 E)}) := by
  intro E _ _ _ 𝔍 M h𝔍 hM
  have hK : Ideal.span {(M : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM.ne'
  exact exists_span_eq_mul_coprime 𝔍 _ h𝔍 hK

end GlobalTheory.Dict
