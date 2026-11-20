import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Matrix.IsDiag
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
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.FrameSort

theorem exists_antitone_reorder : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by
  intro n U₀ d hU
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), Antitone (d ∘ σ) := by
    refine ⟨Tuple.sort (fun i => - d i), ?_⟩
    intro a b hab
    have := Tuple.monotone_sort (fun i => - d i) hab
    simpa using this
  have hH : (U₀.submatrix id σ)ᴴ = U₀ᴴ.submatrix σ id := by
    ext i j; simp
  have hconj : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      (U₀.submatrix id σ)ᴴ * Z * U₀.submatrix id σ = (U₀ᴴ * Z * U₀).submatrix σ σ := by
    intro Z
    rw [hH]
    ext i j
    simp [Matrix.mul_apply]
  refine ⟨U₀.submatrix id σ, ?_, d ∘ σ, hσ, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have h1 := hconj 1
    rw [Matrix.mul_one] at h1
    rw [h1, Matrix.mul_one]
    have h2 : U₀ᴴ * U₀ = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.mp hU
      simpa [Matrix.star_eq_conjTranspose] using this
    rw [h2]
    simp
  · rw [hH]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.submatrix_apply, id, Function.comp]
    exact Equiv.sum_comp σ (fun i => U₀ a i * (d i : ℂ) * U₀ᴴ i b)
  · intro Z hZ
    rw [hconj Z]
    intro i j hij
    simpa using hZ (fun e => hij (σ.injective e))

end GlobalTheory.CompanionTheory.FrameSort
