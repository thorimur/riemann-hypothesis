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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem kaehlerD_root_twist (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (ζ : Sˣ) (r : S)
    (N a : ℕ) (hN : 1 ≤ N) (hζ : (ζ : S) ^ N = 1) :
    ((ζ : S) ^ a * r) ^ (N - 1) • KaehlerDifferential.D R S ((ζ : S) ^ a * r) =
      r ^ (N - 1) • KaehlerDifferential.D R S r +
        ((a : S) * r ^ N * ((ζ⁻¹ : Sˣ) : S)) • KaehlerDifferential.D R S (ζ : S) ∧
    (N : S) • (r ^ (N - 1) • KaehlerDifferential.D R S r) = KaehlerDifferential.D R S (r ^ N) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hzi : (ζ : S) * ((ζ⁻¹ : Sˣ) : S) = 1 := Units.mul_inv ζ
  constructor
  · rw [Derivation.leibniz, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S]
    simp only [smul_add, smul_smul]
    congr 2
    · have hw : ((ζ : S) ^ a) ^ (M + 1) = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
      rw [mul_pow]
      linear_combination r ^ M * hw
    · rcases a with _ | b
      · simp
      · have hw : ((ζ : S) ^ (b + 1)) ^ (M + 1) = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        linear_combination ((b : S) + 1) * r ^ (M + 1) *
          (((ζ⁻¹ : Sˣ) : S) * hw - ((ζ : S) ^ (b + 1)) ^ M * (ζ : S) ^ b * hzi)
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul S, Nat.add_sub_cancel]

end GlobalTheory.K5
