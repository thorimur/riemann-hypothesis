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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_ideal_eq_of_span_of_linearIndependent
    (A B R : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] {r : ℕ}
    (v : Fin r → B) (J₁ J₂ : Ideal (R ⊗[A] B)) (h12 : J₁ ≤ J₂)
    (hspan : Submodule.span R (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) = ⊤)
    (hli : LinearIndependent R (fun k => Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k))) :
    J₁ = J₂ := by
  refine le_antisymm h12 (fun t ht => ?_)
  have hmem : Ideal.Quotient.mk J₁ t ∈ Submodule.span R
      (Set.range (fun k => Ideal.Quotient.mk J₁ ((1 : R) ⊗ₜ[A] v k))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hmem
  set s : R ⊗[A] B := ∑ k, c k • ((1 : R) ⊗ₜ[A] v k) with hs
  have hmk : ∀ (J : Ideal (R ⊗[A] B)), Ideal.Quotient.mk J s
      = ∑ k, c k • Ideal.Quotient.mk J ((1 : R) ⊗ₜ[A] v k) := by
    intro J
    rw [hs, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Ideal.Quotient.mkₐ_eq_mk R, map_smul]
  have h1 : t - s ∈ J₁ := by
    rw [← Ideal.Quotient.eq, hmk J₁, hc]
  have h2 : s ∈ J₂ := by
    have := J₂.sub_mem ht (h12 h1)
    simpa using this
  have hsum : ∑ k, c k • Ideal.Quotient.mk J₂ ((1 : R) ⊗ₜ[A] v k) = 0 := by
    rw [← hmk J₂, Ideal.Quotient.eq_zero_iff_mem]; exact h2
  have hc0 : ∀ k, c k = 0 := Fintype.linearIndependent_iff.1 hli c hsum
  have hs0 : s = 0 := by simp [hs, hc0]
  rw [hs0, sub_zero] at h1
  exact h1

end GlobalTheory
