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
import Mathlib.RingTheory.HopfAlgebra.Convolution
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
open scoped TensorProduct

namespace GlobalTheory

open TensorProduct in

theorem isUnit_of_unit_mul_comul_eq_tmul_self (K H : Type) [Field K] [CommRing H] [HopfAlgebra K H]
    (c : H ⊗[K] H) (hc : IsUnit c) (u : H) (hu : u ≠ 0)
    (h : c * Coalgebra.comul (R := K) u = u ⊗ₜ[K] u) : IsUnit u := by

  let φ : H ⊗[K] H →ₐ[K] H :=
    (Algebra.TensorProduct.lid K H).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom K H) (AlgHom.id K H))
  have hφΔ : φ (Coalgebra.comul (R := K) u) = u := by
    have e := congrArg (TensorProduct.lid K H) (Coalgebra.rTensor_counit_comul (R := K) u)
    rw [TensorProduct.lid_tmul, one_smul] at e
    exact e
  have hφuu : φ (u ⊗ₜ[K] u) = Coalgebra.counit (R := K) u • u := by
    simp [φ]
  have hε : Coalgebra.counit (R := K) u ≠ 0 := by
    intro h0
    have e := congrArg φ h
    rw [map_mul, hφΔ, hφuu, h0, zero_smul] at e
    exact hu ((hc.map φ).mul_right_eq_zero.mp e)

  let ψ : H ⊗[K] H →ₐ[K] H :=
    Algebra.TensorProduct.lift (AlgHom.id K H) (HopfAlgebra.antipodeAlgHom K H)
      (fun _ _ => Commute.all _ _)
  have hψΔ : ψ (Coalgebra.comul (R := K) u) = algebraMap K H (Coalgebra.counit (R := K) u) := by
    rw [← HopfAlgebra.mul_antipode_lTensor_comul_apply (R := K) u]
    induction Coalgebra.comul (R := K) u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ψ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hψuu : ψ (u ⊗ₜ[K] u) = u * HopfAlgebra.antipode K u := by
    simp [ψ]
  have e := congrArg ψ h
  rw [map_mul, hψΔ, hψuu] at e
  have hU : IsUnit (u * HopfAlgebra.antipode K u) := by
    rw [← e]
    exact (hc.map ψ).mul ((isUnit_iff_ne_zero.mpr hε).map (algebraMap K H))
  exact isUnit_of_mul_isUnit_left hU

end GlobalTheory
