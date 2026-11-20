import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Central.Matrix
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

namespace DiscreteGroups.T1.Desc.TraceUniqueU3

open Matrix

theorem trace_unique_matrix {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hg : ∀ A B, g (A * B) = g (B * A)) :
    ∃ c : ℂ, ∀ A, g A = c * A.trace := by
  classical
  let Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.Dual ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    LinearMap.mk₂ ℂ (fun C A => (A * C).trace)
      (fun C C' A => by simp only [Matrix.mul_add, Matrix.trace_add])
      (fun c C A => by simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul])
      (fun C A A' => by simp only [Matrix.add_mul, Matrix.trace_add])
      (fun c C A => by simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul])
  have hΦ : ∀ C A, Φ C A = (A * C).trace := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    intro C C' h
    rw [Matrix.ext_iff_trace_mul_left]
    intro X
    have h1 := LinearMap.congr_fun h X
    rw [hΦ, hΦ] at h1
    exact h1
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).1 hinj
  obtain ⟨C, hC⟩ := hsurj g
  have hgC : ∀ A, g A = (A * C).trace := fun A => by rw [← hC, hΦ]
  have hcomm : ∀ B, B * C = C * B := by
    intro B
    rw [Matrix.ext_iff_trace_mul_left]
    intro A
    calc (A * (B * C)).trace = (A * B * C).trace := by rw [Matrix.mul_assoc]
      _ = g (A * B) := (hgC _).symm
      _ = g (B * A) := hg A B
      _ = (B * A * C).trace := hgC _
      _ = (A * C * B).trace := (Matrix.trace_mul_cycle A C B).symm
      _ = (A * (C * B)).trace := by rw [Matrix.mul_assoc]
  have hcen : C ∈ Subalgebra.center ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [Subalgebra.mem_center_iff]
    exact hcomm
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (Algebra.IsCentral.out hcen)
  refine ⟨c, fun A => ?_⟩
  rw [hgC, ← hc, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul]

end DiscreteGroups.T1.Desc.TraceUniqueU3
