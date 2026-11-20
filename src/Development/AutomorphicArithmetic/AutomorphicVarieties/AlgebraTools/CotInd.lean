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

open IsLocalRing

namespace UpperTheory.V.AlgebraTools

structure CotInd (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) : Prop where
  mem : ∀ k, x k ∈ maximalIdeal R
  indep : ∀ a : κ → R, ∑ k, a k * x k ∈ maximalIdeal R ^ 2 → ∀ k, a k ∈ maximalIdeal R

theorem cotInd_iff (R : Type) [CommRing R] [IsLocalRing R] {κ : Type} [Fintype κ] (x : κ → R) :
    CotInd R x ↔ ∃ h : ∀ k, x k ∈ maximalIdeal R,
      LinearIndependent (ResidueField R)
        (fun k => ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)) := by
  have key : ∀ (h : ∀ k, x k ∈ maximalIdeal R) (a : κ → R),
      (∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R) = 0) ↔
        ∑ k, a k * x k ∈ maximalIdeal R ^ 2 := by
    intro h a
    have h1 : ∑ k, residue R (a k) • ((maximalIdeal R).toCotangent ⟨x k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, a k • (⟨x k, h k⟩ : maximalIdeal R)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (a k) _
    rw [h1, Ideal.toCotangent_eq_zero]
    simp
  constructor
  · rintro ⟨h, hi⟩
    refine ⟨h, Fintype.linearIndependent_iff.2 fun g hg k => ?_⟩
    choose a ha using fun k => residue_surjective (g k)
    rw [← ha k, residue_eq_zero_iff]
    refine hi a ((key h a).1 ?_) k
    simpa [ha] using hg
  · rintro ⟨h, hi⟩
    refine ⟨h, fun a ha k => ?_⟩
    have := Fintype.linearIndependent_iff.1 hi (fun k => residue R (a k)) ((key h a).2 ha) k
    exact (residue_eq_zero_iff _).1 this

theorem CotInd.comp {R : Type} [CommRing R] [IsLocalRing R] {κ ι : Type} [Fintype κ] [Fintype ι]
    {x : κ → R} (h : CotInd R x) (e : ι → κ) (he : Function.Injective e) : CotInd R (x ∘ e) := by
  obtain ⟨h1, h2⟩ := (cotInd_iff R x).1 h
  exact (cotInd_iff R _).2 ⟨fun i => h1 (e i), h2.comp e he⟩

end UpperTheory.V.AlgebraTools
