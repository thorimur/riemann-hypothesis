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

namespace GlobalTheory

theorem eq_of_le_of_comap_eq_of_indEtale : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := by
  intro B O _ _ _ ⟨ι, _, _, _, Si, _, hcov, hloc⟩ p p' hp hp' hle hcomap
  by_contra hne
  obtain ⟨x, hx', hx⟩ : ∃ x, x ∈ p' ∧ x ∉ p := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hle h)
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨E, _, _, _, P, _, ⟨e⟩⟩ := hloc i
  haveI : Algebra.QuasiFinite B (Localization.AtPrime P) := inferInstance
  haveI : Algebra.QuasiFinite B (Si i) := (Algebra.QuasiFinite.iff_of_algEquiv e).mp inferInstance
  have key := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := B)
    (p.comap (algebraMap (Si i) O)) (p'.comap (algebraMap (Si i) O)) (Ideal.comap_mono hle)
    (by
      simp only [Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hcomap)
  have h1 : (⟨x, hi⟩ : Si i) ∈ p'.comap (algebraMap (Si i) O) := hx'
  rw [← key] at h1
  exact hx h1

end GlobalTheory
