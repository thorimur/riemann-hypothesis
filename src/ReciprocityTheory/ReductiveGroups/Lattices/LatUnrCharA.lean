import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable section

namespace ReciprocityTheory.ChartRestriction.T1

open NumberField IsDedekindDomain Polynomial

theorem lat_charpoly_blockDiagonal {R n o : Type*} [CommRing R] [Fintype n] [DecidableEq n] [Fintype o]
    [DecidableEq o] (M : o → Matrix n n R) :
    (Matrix.blockDiagonal M).charpoly = ∏ k, (M k).charpoly := by
  have h : (Matrix.blockDiagonal M).charmatrix = Matrix.blockDiagonal fun k => (M k).charmatrix := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    by_cases hk : k = k'
    · subst hk
      by_cases hij : i = j
      · subst hij
        simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply]
      · simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply, hij]
    · simp [Matrix.charmatrix_apply, Matrix.blockDiagonal_apply, Matrix.diagonal_apply, hk]
  rw [Matrix.charpoly, h, Matrix.det_blockDiagonal]
  rfl

theorem lat_charpoly_lmul_field {K F : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F] (x : F) :
    LinearMap.charpoly (Algebra.lmul K F x) = (minpoly K x) ^ Module.finrank (IntermediateField.adjoin K {x}) F := by
  classical
  have hx : IsIntegral K x := IsIntegral.of_finite K x
  let pb := IntermediateField.adjoin.powerBasis hx
  let c := Module.finBasis (IntermediateField.adjoin K {x}) F
  have hgen : algebraMap (IntermediateField.adjoin K {x}) F pb.gen = x := by
    rw [IntermediateField.adjoin.powerBasis_gen]
    rfl
  have key := Algebra.smulTower_leftMulMatrix_algebraMap pb.basis c pb.gen
  rw [hgen] at key
  rw [← LinearMap.charpoly_toMatrix (Algebra.lmul K F x) (pb.basis.smulTower c),
    ← Algebra.leftMulMatrix_apply, key]
  rw [lat_charpoly_blockDiagonal, Finset.prod_const, Finset.card_univ, charpoly_leftMulMatrix,
    IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, Fintype.card_fin]

variable {E : Type} [Field E] [NumberField E]

def lat_cp (θ : 𝓞 E) : Polynomial ℤ := LinearMap.charpoly (Algebra.lmul ℤ (𝓞 E) θ)

theorem lat_cp_natDegree (θ : 𝓞 E) : (lat_cp θ).natDegree = Module.finrank ℚ E := by
  rw [lat_cp, LinearMap.charpoly_natDegree, NumberField.RingOfIntegers.rank]

theorem lat_cp_map (θ : 𝓞 E) :
    (lat_cp θ).map (algebraMap ℤ ℚ) = LinearMap.charpoly (Algebra.lmul ℚ E (θ : E)) := by
  classical
  rw [lat_cp, ← LinearMap.charpoly_toMatrix (Algebra.lmul ℤ (𝓞 E) θ) (RingOfIntegers.basis E),
    ← Matrix.charpoly_map, ← LinearMap.charpoly_toMatrix (Algebra.lmul ℚ E (θ : E)) (integralBasis E)]
  congr 1
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, integralBasis_apply]
  have e : Algebra.lmul ℚ E (θ : E) (algebraMap (𝓞 E) E (RingOfIntegers.basis E j)) =
      algebraMap (𝓞 E) E (Algebra.lmul ℤ (𝓞 E) θ (RingOfIntegers.basis E j)) := by
    first
    | rfl
    | simp [map_mul]
  rw [e, integralBasis_repr_apply]

theorem lat_cp_eq_minpoly_pow (θ : 𝓞 E) : ∃ r : ℕ, 1 ≤ r ∧ lat_cp θ = (minpoly ℤ θ) ^ r := by
  refine ⟨Module.finrank (IntermediateField.adjoin ℚ {(θ : E)}) E, Module.finrank_pos, ?_⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [lat_cp_map, lat_charpoly_lmul_field, Polynomial.map_pow,
    ← minpoly.isIntegrallyClosed_eq_field_fractions ℚ E (RingOfIntegers.isIntegral θ)]

end ReciprocityTheory.ChartRestriction.T1

end
