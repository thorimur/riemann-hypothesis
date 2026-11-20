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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory

def killersEquiv {k : Type} [Field k] {m n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    {w : Matrix (Fin m) (Fin n) k // w * A = 0} ≃ (Fin m → LinearMap.ker (Aᵀ).mulVecLin) where
  toFun w i := ⟨w.1 i, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
    funext l
    have := congrFun (congrFun w.2 i) l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  invFun f := ⟨Matrix.of fun i => (f i).1, by
    ext i l
    have h := (f i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at h
    have := congrFun h l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  left_inv w := by ext i l; rfl
  right_inv f := by ext i l; rfl

theorem natCard_matrices_mul_eq_zero (k : Type) [Field k] [Finite k] (m n j : ℕ)
    (A : Matrix (Fin n) (Fin n) k)
    (h : Module.finrank k (LinearMap.range A.mulVecLin) + j = n) :
    Nat.card {w : Matrix (Fin m) (Fin n) k // w * A = 0} = Nat.card k ^ (j * m) := by
  have h1 : Module.finrank k (LinearMap.range (Aᵀ).mulVecLin)
      = Module.finrank k (LinearMap.range A.mulVecLin) := Matrix.rank_transpose A
  have h2 := LinearMap.finrank_range_add_finrank_ker (Aᵀ).mulVecLin
  rw [h1, Module.finrank_fin_fun] at h2
  have h3 : Module.finrank k (LinearMap.ker (Aᵀ).mulVecLin) = j := by omega
  rw [Nat.card_congr (killersEquiv A), Nat.card_fun, Module.natCard_eq_pow_finrank (K := k), h3,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, pow_mul]

end GlobalTheory
