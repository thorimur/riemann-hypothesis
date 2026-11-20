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
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.GaussInt

theorem gaussSum_mul_gaussSum_inv_of_isPrimitive {K : Type} [Field K] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter K N} {ψ : AddChar (ZMod N) K} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (N : K) := by
  have h1 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹
      = ∑ b : ZMod N, ∑ a : ZMod N, χ a * ψ (b * (a - 1)) := by
    conv_lhs => rw [gaussSum.eq_1 χ⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, mul_comm (gaussSum χ ψ), ← gaussSum_mulShift_of_isPrimitive ψ hχ b,
      gaussSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AddChar.mulShift_apply, AddChar.inv_apply, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [h1, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]
  rw [Finset.sum_eq_single (1 : ZMod N)]
  · simp
  · intro a _ ha
    simp [ha]
  · simp

end GlobalTheory.GaussInt
