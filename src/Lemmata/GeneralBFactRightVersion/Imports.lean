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

namespace Bl.general_b_fact_right_version

theorem goal1 :
  ∀ {E Ω : Type} [inst : Field.{0} E] [inst_1 : Field.{0} Ω] [inst_2 : Algebra.{0, 0} E Ω] (σ : AlgEquiv.{0, 0, 0} E Ω Ω)
  (y : Ω),
  IsIntegral.{0, 0} E y →
    Exists.{1} fun (n : Nat) ↦ And (Ne.{1} n 0) (Eq.{1} (DFunLike.coe.{1, 1, 1} (HPow.hPow.{0, 0, 0} σ n) y) y) := by
  intro E Ω _ _ _ σ y hy
  have hmem : ∀ k : ℕ, (σ ^ k) y ∈ (minpoly E y).rootSet Ω := by
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hy, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) y (minpoly E y)
    rw [minpoly.aeval, map_zero] at h
    simpa using h
  obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => (σ ^ k) y) hmem (Polynomial.rootSet_finite _ _)
  refine ⟨b - a, by omega, ?_⟩
  have hb : b = a + (b - a) := by omega
  rw [hb, pow_add, AlgEquiv.mul_apply] at he
  exact ((σ ^ a).injective he).symm

end Bl.general_b_fact_right_version
