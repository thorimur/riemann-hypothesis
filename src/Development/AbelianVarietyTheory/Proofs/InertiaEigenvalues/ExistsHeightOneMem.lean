import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.HeightOnePrimeMembership

open NumberField

theorem exists_heightOne_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : Nat.Prime p) :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (RingOfIntegers E),
      (p : RingOfIntegers E) ∈ w.asIdeal := by
  have hnu : ¬ IsUnit (p : RingOfIntegers E) := by
    intro hu
    have h1 : IsUnit (Algebra.norm ℤ (p : RingOfIntegers E)) := hu.map _
    have h2 : (p : RingOfIntegers E) = algebraMap ℤ (RingOfIntegers E) (p : ℤ) := by simp
    rw [h2, Algebra.norm_algebraMap] at h1
    have hpos : Module.finrank ℤ (RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (p : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit h3
  have hne : Ideal.span {(p : RingOfIntegers E)} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : (p : RingOfIntegers E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  have hp0 : (p : RingOfIntegers E) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  intro hb
  rw [hb] at hmem
  exact hp0 (by simpa using hmem)

end GlobalTheory.HeightOnePrimeMembership
