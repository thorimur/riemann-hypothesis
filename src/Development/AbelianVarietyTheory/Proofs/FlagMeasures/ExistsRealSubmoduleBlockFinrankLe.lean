import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

open Finset

namespace GlobalTheory

theorem exists_real_submodule_block_finrank_le :
    ∀ (n : ℕ) (E E' : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ 2 * Module.finrank ℂ E' * Module.finrank ℂ E ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        E'.starProjection ∘L T ∘L E.starProjection ∈ U := by
  intro n E E'
  let f : (E →L[ℂ] E') →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E'.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun M N => by ext; simp
      map_smul' := fun c M => by ext; simp }
  refine ⟨LinearMap.range f, ?_, fun T => ⟨E'.orthogonalProjection ∘L T ∘L E.subtypeL, rfl⟩⟩
  refine (LinearMap.finrank_range_le f).trans (le_of_eq ?_)
  have h1 : Module.finrank ℂ (E →L[ℂ] E') = Module.finrank ℂ E * Module.finrank ℂ E' := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E) (F' := E')).finrank_eq,
      Module.finrank_linearMap]
  rw [← Module.finrank_mul_finrank ℝ ℂ (E →L[ℂ] E'), Complex.finrank_real_complex, h1]
  ring

end GlobalTheory
