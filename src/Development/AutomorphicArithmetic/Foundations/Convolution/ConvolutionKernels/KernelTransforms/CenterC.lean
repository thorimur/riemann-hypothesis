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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem centerC_ex (A : Type) [Ring A] [Algebra ℝ A] (z : ℂ ⊗[ℝ] A) :
    ∃ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c x =>
    refine ⟨c.re • x, c.im • x, ?_⟩
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    apply Complex.ext <;> simp
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    refine ⟨a + c, b + d, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

private theorem centerC_uniq (A : Type) [Ring A] [Algebra ℝ A] (a b c d : A)
    (h : (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b = (1 : ℂ) ⊗ₜ[ℝ] c + Complex.I ⊗ₜ[ℝ] d) :
    a = c ∧ b = d := by
  have h1 := congrArg (fun w => TensorProduct.lid ℝ A (LinearMap.rTensor A Complex.reLm w)) h
  have h2 := congrArg (fun w => TensorProduct.lid ℝ A (LinearMap.rTensor A Complex.imLm w)) h
  simp at h1 h2
  exact ⟨h1, h2⟩

theorem UpperTheory.ConvolutionTheory.Tf.centerC :
    ∀ (A : Type) [Ring A] [Algebra ℝ A] (z : ℂ ⊗[ℝ] A), (∃ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b) ∧
      ∀ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b →
        (z ∈ Subalgebra.center ℂ (ℂ ⊗[ℝ] A) ↔ a ∈ Subalgebra.center ℝ A ∧ b ∈ Subalgebra.center ℝ A) := by
  intro A _ _ z
  refine ⟨centerC_ex A z, ?_⟩
  rintro a b rfl
  simp only [Subalgebra.mem_center_iff]
  constructor
  · intro h
    have key : ∀ x : A, x * a = a * x ∧ x * b = b * x := by
      intro x
      have hx := h ((1 : ℂ) ⊗ₜ[ℝ] x)
      simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at hx
      exact centerC_uniq A _ _ _ _ hx
    exact ⟨fun x => (key x).1, fun x => (key x).2⟩
  · rintro ⟨ha, hb⟩ w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ha x, hb x,
        mul_comm c Complex.I]
    | add x y hx hy => rw [add_mul, mul_add (_ + _) x y, hx, hy]
