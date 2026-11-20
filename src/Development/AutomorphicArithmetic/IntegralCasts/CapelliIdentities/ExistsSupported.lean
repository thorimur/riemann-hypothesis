import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.ClassNumber
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

theorem UpperTheory.Reformulated.B.Qo8.exists_supported :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
    ∃ (π : NumberField.RingOfIntegers F),
      π ≠ (0 : NumberField.RingOfIntegers F) ∧
        π ∈ p.asIdeal ∧
          ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), v ≠ p → π ∉ v.asIdeal := by
  intro F _ _ p
  have hp : p.asIdeal ∈ nonZeroDivisors (Ideal (NumberField.RingOfIntegers F)) :=
    mem_nonZeroDivisors_of_ne_zero p.ne_bot
  obtain ⟨n, hn, hpow⟩ :=
    (isOfFinOrder_of_finite (ClassGroup.mk0 ⟨p.asIdeal, hp⟩)).exists_pow_eq_one
  rw [← map_pow] at hpow
  have hprin : (p.asIdeal ^ n).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff (pow_mem hp n)).1 hpow
  obtain ⟨π, hπ⟩ := hprin
  have hπ' : p.asIdeal ^ n = Ideal.span {π} := hπ
  have hmem : π ∈ p.asIdeal ^ n := hπ' ▸ Ideal.mem_span_singleton_self π
  refine ⟨π, ?_, Ideal.pow_le_self hn.ne' hmem, ?_⟩
  · rintro rfl
    rw [Ideal.span_singleton_zero] at hπ'
    exact pow_ne_zero n p.ne_bot hπ'
  · intro v hv hπv
    have hle : p.asIdeal ^ n ≤ v.asIdeal := by
      rw [hπ', Ideal.span_le, Set.singleton_subset_iff]
      exact hπv
    have hle' : p.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le hle
    exact hv (IsDedekindDomain.HeightOneSpectrum.ext
      (p.isMaximal.eq_of_le v.isPrime.ne_top hle').symm)
