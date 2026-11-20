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

theorem UpperTheory.Reformulated.B.Qk41.precomplete_of_pow_le :
    ∀ {A : Type} [inst : CommRing A]
    {I J : Ideal A}, J ≤ I → ∀ {e : ℕ}, I ^ e ≤ J → ∀ [IsPrecomplete J A], IsPrecomplete I A := by
  intro A _ I J hJI e he hJ
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    SModEq.mono (Submodule.smul_mono_left (h1 m)) (hf (Nat.mul_le_mul_left _ hmn)))
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos e))).trans
    (SModEq.mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)) (hL n))
