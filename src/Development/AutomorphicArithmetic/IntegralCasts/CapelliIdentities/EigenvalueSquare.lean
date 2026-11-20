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
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.EigenvalueSquare.eig_sq :
    ∀ {A : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℂ},
    Star.star A * A = (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℂ) →
      ∀ (r : ℝ), Polynomial.eval (↑r : ℂ) A.charpoly = (0 : ℂ) → r ^ (2 : ℕ) = (1 : ℝ) := by
  intro A hA r hr
  rw [Matrix.eval_charpoly] at hr
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hr
  have hAv : A.mulVec v = (r : ℂ) • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hz
    rw [← hz]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h1 : star (A.mulVec v) ⬝ᵥ A.mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hA, Matrix.one_mulVec]
  have h2 : star v ⬝ᵥ v ≠ 0 := by
    open ComplexOrder in
    exact fun h => hv (dotProduct_star_self_eq_zero.mp h)
  rw [hAv, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc] at h1
  have h3 : star (r : ℂ) * (r : ℂ) = 1 := mul_right_cancel₀ h2 (by rw [h1, one_mul])
  rw [Complex.star_def, Complex.conj_ofReal] at h3
  have h4 : r * r = 1 := by exact_mod_cast h3
  rw [sq, h4]
