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

theorem UpperTheory.Reformulated.B.SpanDenominator.den_of_span :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {i : ℕ} (P : Ideal (NumberField.RingOfIntegers K))
      [inst_2 : P.IsPrime] (M : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      ∀
        x ∈
          Submodule.span ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
            (↑M : Set (Fin i → K)),
        ∃ s ∈ P.primeCompl, s • x ∈ M := by
  intro K _ _ i P _ M x hx
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span P.primeCompl
    ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
    (↑M : Set (Fin i → K)) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, t.2, ht⟩
