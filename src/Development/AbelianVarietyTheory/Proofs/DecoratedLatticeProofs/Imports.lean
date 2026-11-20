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

namespace GlobalTheory.ExistsPrimeMem

theorem exists_prime_mem {A : Type} [inst : CommRing A] (P : Ideal A) (hP : Ideal.IsPrime P) :
    ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : A) ∈ P → ∃ (ℓ : ℕ), Nat.Prime ℓ ∧ (↑ℓ : A) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases h1 : n = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hnP)) hP.ne_top
    · have hp := Nat.minFac_prime h1
      have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hsplit : ((n : ℕ) : A) = (n.minFac : A) * ((n / n.minFac : ℕ) : A) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.minFac_dvd n)]
      rw [hsplit] at hnP
      rcases hP.mem_or_mem hnP with h | h
      · exact ⟨n.minFac, hp, h⟩
      · exact ih (n / n.minFac) (Nat.div_lt_self hpos hp.one_lt)
          (Nat.div_pos (Nat.minFac_le hpos) (Nat.minFac_pos n)).ne' h

end GlobalTheory.ExistsPrimeMem
