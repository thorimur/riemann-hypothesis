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

open Matrix

namespace GlobalTheory.CompanionTheory.QR

theorem exists_unitary_mul_blockTriangular {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (_hg : IsUnit g) :
    ∃ k ∈ Matrix.unitaryGroup (Fin m) ℂ, ∃ b : Matrix (Fin m) (Fin m) ℂ,
      g = k * b ∧ b.BlockTriangular id := by
  let e := EuclideanSpace.basisFun (Fin m) ℂ
  let f : Fin m → EuclideanSpace ℂ (Fin m) := fun j => WithLp.toLp 2 fun i => g i j
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by simp
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨e.toBasis.toMatrix o, e.toMatrix_orthonormalBasis_mem_unitary o, o.toBasis.toMatrix f, ?_,
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f⟩
  have hmul := Module.Basis.toMatrix_mul_toMatrix e.toBasis o.toBasis f
  rw [OrthonormalBasis.coe_toBasis] at hmul
  rw [hmul]
  ext i j
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]

end GlobalTheory.CompanionTheory.QR
