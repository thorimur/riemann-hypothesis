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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.AlgHomEqEval

theorem algHom_eq_eval : ∀ {K : Type} [inst : Field K] {P : Type} [Fintype P] [DecidableEq P]
    (θ : (P → K) →ₐ[K] K), ∃ (p : P), ∀ (z : P → K), (θ : (P → K) → K) z = z p := by
  intro K _ P _ _ θ
  have hsum : ∑ p, (Pi.single p (1:K) : P → K) = 1 := by
    ext x; simp [Finset.sum_apply, Pi.single_apply]
  have h1 : ∑ p, θ (Pi.single p 1) = 1 := by
    rw [← map_sum, hsum, map_one]
  obtain ⟨p, -, hp⟩ : ∃ p ∈ Finset.univ, θ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    rw [Finset.sum_eq_zero h] at h1
    exact zero_ne_one h1
  refine ⟨p, fun z => ?_⟩
  have hz : z * Pi.single p 1 = (algebraMap K (P → K) (z p)) * Pi.single p 1 := by
    ext x
    by_cases hx : x = p
    · subst hx; simp
    · simp [Pi.single_apply, hx]
  have h2 := congrArg θ hz
  rw [map_mul, map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at h2
  exact mul_right_cancel₀ hp h2

end GlobalTheory.AlgHomEqEval
