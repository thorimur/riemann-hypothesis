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
import Mathlib.LinearAlgebra.Matrix.Nonsingular
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
open TensorProduct

namespace GlobalTheory.CompanionTheory.Perf

theorem map_eq_zero_of_comp_injective_of_finrank_eq :
    ∀ (A W N : Type) [CommRing A] [Nontrivial A] [AddCommGroup W] [Module A W] [AddCommGroup N]
      [Module A N] [Module.Free A W] [Module.Finite A W] [Module.Free A N] (g : ℕ)
      (φ : (Fin g → A) →ₗ[A] W) (f : W →ₗ[A] N),
      Module.finrank A W = g → Function.Injective φ → f ∘ₗ φ = 0 → f = 0 := by
  intro A W N _ _ _ _ _ _ _ _ _ g φ f hg hφ hf
  classical
  let e : W ≃ₗ[A] (Fin g → A) := (Module.finBasisOfFinrankEq A W hg).equivFun
  let M : Matrix (Fin g) (Fin g) A := LinearMap.toMatrix' (e.toLinearMap ∘ₗ φ)
  have hM : ∀ v, Matrix.mulVec M v = e (φ v) := fun v => by
    change Matrix.toLin' M v = _
    rw [Matrix.toLin'_toMatrix']
    rfl
  have hinj : Function.Injective M.mulVec := by
    intro v v' h
    rw [hM, hM] at h
    exact hφ (e.injective h)
  have hdet : M.det ∈ nonZeroDivisors A :=
    Matrix.nonsingular_iff_det_mem_nonZeroDivisors.mp
      (Matrix.Nonsingular.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp hinj))
  have hkill : ∀ w, M.det • f w = 0 := by
    intro w
    have h1 : φ (M.cramer (e w)) = M.det • w := by
      apply e.injective
      rw [← hM, Matrix.mulVec_cramer, map_smul]
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun hf _
  ext w
  apply (Module.Free.chooseBasis A N).repr.injective
  ext i
  have h2 := congrArg (fun n => (Module.Free.chooseBasis A N).repr n i) (hkill w)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h2
  simpa using (mul_left_mem_nonZeroDivisors_eq_zero_iff hdet).mp h2

end GlobalTheory.CompanionTheory.Perf
