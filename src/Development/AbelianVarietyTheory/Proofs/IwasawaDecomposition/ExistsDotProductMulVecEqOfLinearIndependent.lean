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

namespace GlobalTheory

theorem exists_dotProduct_mulVec_eq_of_linearIndependent :
    ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 →
      LinearIndependent ℚ ε → ∀ t : Fin k → ℚ,
      ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by
  intro r k Mq ε hM hε t
  have hU : IsUnit Mq := (Matrix.isUnit_iff_isUnit_det Mq).2 (Ne.isUnit hM)
  have hinj : Function.Injective Mq.mulVecLin := Matrix.mulVec_injective_iff_isUnit.2 hU
  have hli : LinearIndependent ℚ (fun i => Mq *ᵥ ε i) :=
    hε.map' Mq.mulVecLin (LinearMap.ker_eq_bot.2 hinj)
  let U : Matrix (Fin k) (Fin r) ℚ := Matrix.of fun i => Mq *ᵥ ε i
  have hrow : LinearIndependent ℚ U.row := hli
  have hrank : U.rank = Fintype.card (Fin k) := hrow.rank_matrix
  have htop : LinearMap.range U.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card]
    exact hrank
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.1 htop t
  refine ⟨x, fun i => ?_⟩
  rw [dotProduct_comm, ← hx]
  rfl

end GlobalTheory
