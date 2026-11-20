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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def SubringPrimeMaximal.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subalgebra ℤ K) (q : Ideal O),
    q.IsPrime → q ≠ ⊥ → q.IsMaximal

example : ∃ q : Ideal (⊥ : Subalgebra ℤ ℚ), q.IsPrime ∧ q ≠ ⊥ := by
  let e := Algebra.botEquivOfInjective (R := ℤ) (A := ℚ) Int.cast_injective
  have : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  refine ⟨Ideal.comap (e : (⊥ : Subalgebra ℤ ℚ) →+* ℤ) (Ideal.span {2}), Ideal.comap_isPrime _ _, ?_⟩
  intro h
  have hm : (2 : (⊥ : Subalgebra ℤ ℚ)) ∈
      Ideal.comap (e : (⊥ : Subalgebra ℤ ℚ) →+* ℤ) (Ideal.span {2}) := by
    rw [Ideal.mem_comap, map_ofNat]
    exact Ideal.mem_span_singleton_self 2
  rw [h, Ideal.mem_bot] at hm
  have := congrArg Subtype.val hm
  norm_num at this

end GroundTheory.Heights₂.Heights
