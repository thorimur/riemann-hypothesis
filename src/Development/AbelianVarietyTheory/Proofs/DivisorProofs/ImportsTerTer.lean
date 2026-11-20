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

namespace GlobalTheory.LocalUnitApproximation

open NumberField

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {n : ℕ} (M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)) {y : Fin n → K}, y ∈ Submodule.span K (↑M : Set (Fin n → K)) → ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • y ∈ M := by
  intro K _ _ n M y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (x + z) = d₂ • (d₁ • x) + d₁ • (d₂ • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm d₁ d₂ x]
    rw [e]
    exact M.add_mem (M.smul_mem _ h₁) (M.smul_mem _ h₂)
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨num, den⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) a
    simp only at hnd
    have hden : (den : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero den
    refine ⟨(den : 𝓞 K) * d, mul_ne_zero hden hd, ?_⟩
    have e : ((den : 𝓞 K) * d) • (a • x) = num • (d • x) := by
      rw [← algebraMap_smul K ((den : 𝓞 K) * d) (a • x), ← algebraMap_smul K num (d • x),
        ← algebraMap_smul K d x, smul_smul, smul_smul]
      congr 1
      rw [map_mul, ← hnd]
      ring
    rw [e]
    exact M.smul_mem _ h

end GlobalTheory.LocalUnitApproximation
