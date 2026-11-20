import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.sqExt :
    ∀ {K : Type} [Field K], ∃ j : PowerSeries K →+* PowerSeries K, Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ j PowerSeries.X = PowerSeries.X ^ 2 := by
  intro K _
  refine ⟨(PowerSeries.expand 2 two_ne_zero (R := K)).toRingHom, ?_, ?_, ?_, by simp⟩
  · intro f g h
    ext m
    have h1 := congrArg (PowerSeries.coeff (2 * m)) h
    simpa using h1
  · refine ⟨fun f hf => ?_⟩
    rw [PowerSeries.isUnit_iff_constantCoeff] at hf ⊢
    simpa using hf
  · classical
    letI inst : Module (PowerSeries K) (PowerSeries K) :=
      (PowerSeries.expand 2 two_ne_zero (R := K)).toRingHom.toAlgebra.toModule
    have hs : Submodule.span (PowerSeries K) ({1, PowerSeries.X} : Set (PowerSeries K)) = ⊤ := by
      rw [eq_top_iff]
      intro f _
      rw [Submodule.mem_span_pair]
      refine ⟨PowerSeries.mk fun m => PowerSeries.coeff (2 * m) f,
        PowerSeries.mk fun m => PowerSeries.coeff (2 * m + 1) f, ?_⟩
      change PowerSeries.expand 2 two_ne_zero (PowerSeries.mk fun m => PowerSeries.coeff (2 * m) f) * 1 +
        PowerSeries.expand 2 two_ne_zero (PowerSeries.mk fun m => PowerSeries.coeff (2 * m + 1) f) *
          PowerSeries.X = f
      ext n
      rw [mul_one, map_add, ← pow_one (PowerSeries.X (R := K)), PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_expand, PowerSeries.coeff_expand]
      simp only [PowerSeries.coeff_mk]
      split_ifs <;> first | omega | (simp only [add_zero, zero_add]; congr; omega)
    exact ⟨⟨{1, PowerSeries.X}, by rw [Finset.coe_insert, Finset.coe_singleton]; exact hs⟩⟩
