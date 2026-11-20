import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
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

noncomputable section

open NumberField

namespace PI.VolStabSW

def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1

def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)

def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0

theorem chInf_of (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnd χ hχ h1 x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have hI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let g : F →+ ℂ := AddMonoidHom.mk' (fun a => ℓ (algebraMap F (InfiniteAdeleRing F) a) /
    (2 * Real.pi * Complex.I)) (by intro a b; simp only [map_add, add_div])
  have hint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have he : Complex.exp (ℓ (algebraMap F (InfiniteAdeleRing F) a)) = 1 := by
      rw [← hℓ]
      exact h1 a ha
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
    refine ⟨n, ?_⟩
    show ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = n
    rw [hn, mul_div_assoc, div_self hI, mul_one]
  have hg := hA F Λ hne hnd g hint
  have hzero : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h := hg a
    change ℓ (algebraMap F (InfiniteAdeleRing F) a) / (2 * Real.pi * Complex.I) = 0 at h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hI
  have hdense : DenseRange (algebraMap F (InfiniteAdeleRing F)) := by
    first
      | exact InfiniteAdeleRing.denseRange_algebraMap F
      | exact InfiniteAdeleRing.denseRange_algebraMap
      | exact NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have hx : ℓ x = 0 :=
    hdense.induction_on x (isClosed_eq hℓc continuous_const) hzero
  rw [hℓ, hx, Complex.exp_zero]

end PI.VolStabSW
