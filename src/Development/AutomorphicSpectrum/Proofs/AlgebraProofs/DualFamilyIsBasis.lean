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
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg

theorem linearIndependent_span_of_dual_unit :
    ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ)
      (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V),
      IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) →
      LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  intro V _ L _ _ n b u f N hN hf
  classical

  let U : Matrix (Fin n) (Fin n) V := Matrix.of fun i k => b.repr (u i) k
  let F : Matrix (Fin n) (Fin n) V := Matrix.of fun k j => f j (b k)
  have hUF : U * F = N • (1 : Matrix (Fin n) (Fin n) V) := by
    ext i j
    have h1 : f j (u i) = ∑ k, b.repr (u i) k * f j (b k) := by
      calc f j (u i) = f j (∑ k, b.repr (u i) k • b k) := by rw [b.sum_repr]
        _ = ∑ k, b.repr (u i) k * f j (b k) := by
          simp only [map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.mul_apply, U, F, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [← h1, hf]
    split_ifs <;> simp
  have hdet : IsUnit U.det := by
    have h2 : U.det * F.det = N ^ n := by
      rw [← Matrix.det_mul, hUF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact isUnit_of_mul_isUnit_left (h2 ▸ hN.pow n)
  have hb : b.toMatrix u = U.transpose := by
    ext k i
    simp [Module.Basis.toMatrix_apply, U]
  have hdet' : IsUnit (b.toMatrix u).det := by
    rw [hb, Matrix.det_transpose]; exact hdet
  have hdet2 : IsUnit (b.det u) := by
    rw [Module.Basis.det_apply]; exact hdet'
  exact (Module.Basis.is_basis_iff_det b).mpr hdet2

end GlobalTheory.CompanionTheory.CommAlg
