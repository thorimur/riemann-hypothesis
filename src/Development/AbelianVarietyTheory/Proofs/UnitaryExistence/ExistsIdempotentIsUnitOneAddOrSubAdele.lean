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
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdIdem

theorem local_val {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) (s : K) :
    ∃ e : K, (e = 0 ∨ e = 1) ∧ w (1 + 1) ≤ w (e * (1 + s) + (1 - e) * (1 - s)) := by
  have h2 : (1 + 1 : K) = (1 + s) + (1 - s) := by ring
  have h := w.map_add (1 + s) (1 - s)
  rw [← h2] at h
  rcases le_total (w (1 - s)) (w (1 + s)) with hle | hle
  · refine ⟨1, Or.inr rfl, ?_⟩
    rw [max_eq_left hle] at h
    simpa using h
  · refine ⟨0, Or.inl rfl, ?_⟩
    rw [max_eq_right hle] at h
    simpa using h

theorem local_field {K : Type*} [Field K] (h2 : (1 + 1 : K) ≠ 0) (s : K) :
    ∃ e : K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  by_cases h : 1 + s = 0
  · refine ⟨0, by simp, ?_⟩
    rw [isUnit_iff_ne_zero]
    intro h'
    apply h2
    linear_combination h + h'
  · exact ⟨1, by simp, by simpa [isUnit_iff_ne_zero] using h⟩

theorem finite_part (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [CharZero K] [Algebra R K]
    [IsFractionRing R K] (s : FiniteAdeleRing R K) :
    ∃ e : FiniteAdeleRing R K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  have hu : IsUnit (1 + 1 : FiniteAdeleRing R K) := by
    have : IsUnit (1 + 1 : K) := by
      rw [isUnit_iff_ne_zero]; norm_num
    simpa using this.map (algebraMap K (FiniteAdeleRing R K))
  rw [FiniteAdeleRing.isUnit_iff] at hu
  choose e he hv using fun v : HeightOneSpectrum R =>
    local_val (Valued.v : Valuation (v.adicCompletion K) _) (s v)
  have hint : ∀ v : HeightOneSpectrum R, e v ∈ v.adicCompletionIntegers K := by
    intro v
    rcases he v with h | h <;> rw [h]
    · exact zero_mem _
    · exact one_mem _
  let E : FiniteAdeleRing R K := ⟨e, Filter.Eventually.of_forall hint⟩
  refine ⟨E, ?_, ?_⟩
  · refine FiniteAdeleRing.ext K fun v => ?_
    change e v * e v = e v
    rcases he v with h | h <;> simp [h]
  · have hval : ∀ v : HeightOneSpectrum R, Valued.v ((1 + 1 : FiniteAdeleRing R K) v) ≤
        Valued.v ((E * (1 + s) + (1 - E) * (1 - s)) v) := fun v => hv v
    rw [FiniteAdeleRing.isUnit_iff]
    refine ⟨fun v h0 => ?_, ?_⟩
    · have := hval v
      rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
      exact hu.1 v this
    · filter_upwards [hu.2, (E * (1 + s) + (1 - E) * (1 - s)).2] with v h1 h2
      exact le_antisymm h2 (h1 ▸ hval v)

theorem infinite_part (K : Type*) [Field K] [CharZero K] (s : InfiniteAdeleRing K) :
    ∃ e : InfiniteAdeleRing K, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  have h2 : ∀ v : InfinitePlace K, (1 + 1 : v.Completion) ≠ 0 := by
    intro v h
    have : algebraMap K v.Completion (1 + 1) = 0 := by rw [map_add, map_one]; exact h
    rw [map_eq_zero] at this
    norm_num at this
  choose e he hu using fun v : InfinitePlace K => local_field (h2 v) (s v)
  exact ⟨e, funext he, Pi.isUnit_iff.2 hu⟩

theorem exists_idem_isUnit (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F) :
    ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  obtain ⟨e₁, h₁, u₁⟩ := infinite_part F s.1
  obtain ⟨e₂, h₂, u₂⟩ := finite_part (𝓞 F) F s.2
  exact ⟨(e₁, e₂), Prod.ext h₁ h₂, Prod.isUnit_iff.2 ⟨u₁, u₂⟩⟩

end GlobalTheory.AdIdem
