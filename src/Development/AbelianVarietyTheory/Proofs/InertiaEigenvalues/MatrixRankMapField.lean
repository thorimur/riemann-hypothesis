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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
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
private lemma rank_fromBlocks_one_zero_lemma {F G : Type} [Field F] [Field G] (r s : ℕ) :
    (fromBlocks (1 : Matrix (Fin r) (Fin r) F) 0 0 (0 : Matrix (Fin s) (Fin s) F)).rank =
      (fromBlocks (1 : Matrix (Fin r) (Fin r) G) 0 0 (0 : Matrix (Fin s) (Fin s) G)).rank := by
  classical
  rw [← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal,
    ← diagonal_one, ← diagonal_zero, fromBlocks_diagonal, rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by cases i <;> simp)
theorem matrix_rank_map_field {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) : (M.map φ).rank = M.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, h⟩ := exists_rank_normal_form M
  have hVd : IsUnit V.det := (isUnit_iff_isUnit_det _).1 hV
  have hUd : IsUnit U.det := (isUnit_iff_isUnit_det _).1 hU
  have hV' : IsUnit (V.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hVd.map φ
  have hU' : IsUnit (U.map φ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hUd.map φ
  have hmap : V.map φ * M.map φ * U.map φ =
      (fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) L) 0 0 0).submatrix e e := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h, ← submatrix_map, fromBlocks_map]
    simp
  calc (M.map φ).rank = (V.map φ * M.map φ * U.map φ).rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hU', rank_mul_eq_right_of_isUnit_det _ _ hV']
    _ = (fromBlocks (1 : Matrix (Fin M.rank) (Fin M.rank) K) 0 0 0).rank := by
        rw [hmap, rank_submatrix]
        exact rank_fromBlocks_one_zero_lemma _ _
    _ = (V * M * U).rank := by rw [h, rank_submatrix]
    _ = M.rank := by
        rw [rank_mul_eq_left_of_isUnit_det _ _ hUd, rank_mul_eq_right_of_isUnit_det _ _ hVd]
end GlobalTheory
