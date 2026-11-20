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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Std.Tactic.BVDecide.Normalize.Prop
open MvPolynomial

namespace GlobalTheory.VandermondeAntisym

theorem prod_Ioi_rev {R : Type*} [CommMonoid R] {n : ℕ} (f : Fin n → Fin n → R) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f (Fin.rev j) (Fin.rev i)) = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f i j := by
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun j => Finset.Iio j) (fun i j => by simp [and_comm])]
  rw [← Equiv.prod_comp (Fin.revPerm (n := n))]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [Fin.revPerm_apply]
  rw [← Fin.map_revPerm_Ioi, Finset.prod_map]
  simp

theorem det_eq (n : ℕ) :
    (Matrix.of fun i j : Fin n => (-X i : MvPolynomial (Fin n) ℝ) ^ (n - 1 - (j : ℕ))).det =
      ∏ i : Fin n, ∏ i' ∈ Finset.Ioi i, ((X i' : MvPolynomial (Fin n) ℝ) - X i) := by
  have h : (Matrix.of fun i j : Fin n => (-X i : MvPolynomial (Fin n) ℝ) ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde (fun i : Fin n => (-X (Fin.rev i) : MvPolynomial (Fin n) ℝ))).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
    rw [Nat.sub_sub, Nat.add_comm 1]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde]
  rw [← prod_Ioi_rev]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Fin.rev_rev]; ring

end GlobalTheory.VandermondeAntisym

open GlobalTheory.VandermondeAntisym in

theorem GlobalTheory.prod_Ioi_sub_eq_antisymm_monomial : ∀ n : ℕ, (∏ i : Fin n, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X i' - MvPolynomial.X i) : MvPolynomial (Fin n) ℝ) = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) • rename σ (∏ i : Fin n, (-MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (n - 1 - (i : ℕ))) := by
  intro n
  rw [← det_eq, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, Int.cast_smul_eq_zsmul ℝ, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  simp
