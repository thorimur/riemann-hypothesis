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

open MonoidAlgebra

theorem groupAlgebra_coeff_mul_fintype {R G : Type} [CommRing R] [Group G] [Fintype G]
    (x y : MonoidAlgebra R G) (a : G) :
    (x * y).coeff a = ∑ c : G, x.coeff (a * c⁻¹) * y.coeff c := by
  classical
  have hs : ∀ (f : G →₀ R) (g : G → R → R), (∀ i, g i 0 = 0) → f.sum g = ∑ i, g i (f i) :=
    fun f g h => Finsupp.sum_fintype f g h
  rw [MonoidAlgebra.coeff_mul, hs _ _ (fun i => by simp)]
  rw [Finset.sum_congr rfl fun b _ => hs _ _ (fun i => by simp)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∀ m : G, (m * c = a) ↔ (m = a * c⁻¹) := fun m => eq_mul_inv_iff_mul_eq.symm
  simp_rw [this]
  simp

theorem groupAlgebra_exists_right_inv_of_map {E L G : Type} [Field E] [Field L] [Group G]
    [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G) :
    (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) →
      ∃ v : MonoidAlgebra E G, x * v = 1 := by
  classical
  rintro ⟨vL, hvL⟩
  let M : Matrix G G E := fun a c => x.coeff (a * c⁻¹)

  have hsurj : Function.Surjective (M.map j).mulVec := by
    intro w
    let y : MonoidAlgebra L G := ofCoeff (Finsupp.equivFunOnFinite.symm w)
    refine ⟨fun c => (vL * y).coeff c, ?_⟩
    funext a
    have h1 : (MonoidAlgebra.mapRingHom G j x * (vL * y)).coeff a = w a := by
      rw [← mul_assoc, hvL, one_mul]
      rfl
    rw [groupAlgebra_coeff_mul_fintype] at h1
    simp only [MonoidAlgebra.coeff_mapRingHom] at h1
    exact h1
  have hU : IsUnit (M.map j) := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hdetL : IsUnit (j M.det) := by
    rw [RingHom.map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet : M.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdetL
    exact not_isUnit_zero hdetL
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM
    (fun a => (1 : MonoidAlgebra E G).coeff a)
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm u), ?_⟩
  apply MonoidAlgebra.ext
  ext a
  rw [groupAlgebra_coeff_mul_fintype]
  have := congrFun hu a
  simpa [Matrix.mulVec, dotProduct, M] using this

end GlobalTheory
