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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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

namespace GlobalTheory.CompanionTheory.Dblock.ComapLat

theorem comap_mulVec_compact_open : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : Matrix (Fin n) (Fin n) k), IsUnit g → ∀ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsCompact ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) ∧ IsOpen ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k)) := by
  intro k _ _ _ _ n g hg A hc ho
  haveI : IsTopologicalRing k := inferInstance
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hcont : ∀ m : Matrix (Fin n) (Fin n) k, Continuous (fun x : Fin n → k => m.mulVec x) :=
    fun m => continuous_const.matrix_mulVec continuous_id
  have hset : ((A.comap (Matrix.mulVecLin g).toAddMonoidHom : AddSubgroup (Fin n → k)) : Set (Fin n → k))
      = (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k)) := rfl
  rw [hset]
  refine ⟨?_, ho.preimage (hcont g)⟩
  have himg : (fun x : Fin n → k => g.mulVec x) ⁻¹' (A : Set (Fin n → k))
      = (fun x : Fin n → k => g⁻¹.mulVec x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.mulVec x, hx, ?_⟩
      simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hdet, Matrix.one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_preimage, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hdet,
        Matrix.one_mulVec]
      exact hy
  rw [himg]
  exact hc.image (hcont g⁻¹)

end GlobalTheory.CompanionTheory.Dblock.ComapLat
