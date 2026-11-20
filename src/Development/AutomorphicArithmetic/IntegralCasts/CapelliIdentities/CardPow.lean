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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.Qi54.card_pow :
    ∀ {E : Type} [inst : Field E] [NumberField E]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (q : ℕ),
    Nat.Prime q →
      (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal →
        ∃ (f : ℕ), Nat.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) = q ^ f := by
  intro E _ _ w q hq hmem
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _
  have h0 : (q : NumberField.RingOfIntegers E ⧸ w.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_natCast] at this
  haveI : CharP (NumberField.RingOfIntegers E ⧸ w.asIdeal) q :=
    (CharP.charP_iff_prime_eq_zero (p := q) (hp := hq)).mpr h0
  obtain ⟨n, -, hn⟩ := FiniteField.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) q
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
