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
import Mathlib.Topology.Sheaves.Presheaf

namespace GlobalTheory.IsolatedTheoremFour

open IsDedekindDomain

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {l : ℕ}, Nat.Prime l → ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), (↑l : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  intro K _ _ l hl
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hker : RingHom.ker (algebraMap ℤ (NumberField.RingOfIntegers K)) ≤ Ideal.span {(l : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int (algebraMap ℤ (NumberField.RingOfIntegers K)))]
    exact bot_le
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {(l : ℤ)}) hker
  have hlQ : ((l : ℕ) : NumberField.RingOfIntegers K) ∈ Q := by
    have h1 : (l : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers K)) := by
      rw [hQc]
      exact Ideal.subset_span rfl
    simpa using h1
  have hl0 : ((l : ℕ) : NumberField.RingOfIntegers K) ≠ 0 := by
    exact_mod_cast hl.ne_zero
  exact ⟨⟨Q, hQ.isPrime, fun h => hl0 (Ideal.mem_bot.mp (h ▸ hlQ))⟩, hlQ⟩

end GlobalTheory.IsolatedTheoremFour
