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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

open Matrix IsLocalRing

theorem dvr_matrix_exists_leftInverse_of_saturated
    (V Fr : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field Fr]
    [Algebra V Fr] [IsFractionRing V Fr] (n m : ℕ) (A : Matrix (Fin n) (Fin m) V)
    (hA : ∀ (cf : Fin m → Fr) (b : Fin n → V),
      (A.map (algebraMap V Fr)).mulVec cf = (fun j => algebraMap V Fr (b j)) →
        ∀ i, ∃ a : V, algebraMap V Fr a = cf i) :
    ∃ B : Matrix (Fin m) (Fin n) V, B * A = 1 := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hinj0 : Function.Injective (algebraMap V Fr) := IsFractionRing.injective V Fr
  have hπF : algebraMap V Fr π ≠ 0 := by
    intro h; exact hπ0 (hinj0 (by rw [h, map_zero]))
  set k := ResidueField V
  set Ab : Matrix (Fin n) (Fin m) k := A.map (residue V) with hAb

  have hker : LinearMap.ker (Matrix.toLin' Ab) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro cb hcb
    rw [Matrix.toLin'_apply] at hcb
    choose c hc using fun j => residue_surjective (R := V) (cb j)
    have hcb' : cb = fun j => residue V (c j) := funext fun j => (hc j).symm
    have hmem : ∀ i, (A.mulVec c) i ∈ maximalIdeal V := by
      intro i
      rw [← residue_eq_zero_iff]
      have := congrFun hcb i
      rw [hcb'] at this
      simpa [Matrix.mulVec, dotProduct, hAb, map_sum] using this
    have hmax : maximalIdeal V = Ideal.span {π} := hπ.maximalIdeal_eq
    have hdiv : ∀ i, π ∣ (A.mulVec c) i := fun i => by
      have := hmem i; rw [hmax, Ideal.mem_span_singleton] at this; exact this
    choose b hb using hdiv
    set cf : Fin m → Fr := fun j => algebraMap V Fr (c j) / algebraMap V Fr π
    have hcf : (A.map (algebraMap V Fr)).mulVec cf = fun j => algebraMap V Fr (b j) := by
      funext i
      have h1 : (A.map (algebraMap V Fr)).mulVec cf i
          = algebraMap V Fr ((A.mulVec c) i) / algebraMap V Fr π := by
        simp only [cf, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
          Finset.sum_div, mul_div_assoc]
      rw [h1, hb i, map_mul, mul_div_assoc, mul_div_cancel₀ _ hπF]
    have hint := hA cf b hcf
    funext j
    obtain ⟨a, ha⟩ := hint j
    have : c j = π * a := by
      apply hinj0
      rw [map_mul, ha]
      simp only [cf]
      field_simp
    rw [hcb']
    simp only [Pi.zero_apply]
    rw [this, map_mul, (residue_eq_zero_iff π).2 hπ.not_isUnit, zero_mul]

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Ab) hker
  set Bb : Matrix (Fin m) (Fin n) k := LinearMap.toMatrix' g
  have hBb : Bb * Ab = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  choose B₀' hB₀ using fun i j => residue_surjective (R := V) (Bb i j)
  set B₀ : Matrix (Fin m) (Fin n) V := Matrix.of B₀'
  have hB₀' : B₀.map (residue V) = Bb := by ext i j; exact hB₀ i j

  have hdet : IsUnit (B₀ * A).det := by
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul,
      hB₀', ← hAb, hBb, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(B₀ * A)⁻¹ * B₀, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]

end GlobalTheory
