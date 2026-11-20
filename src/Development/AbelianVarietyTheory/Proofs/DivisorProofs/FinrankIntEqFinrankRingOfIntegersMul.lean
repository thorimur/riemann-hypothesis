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
open NumberField

namespace GlobalTheory
open TensorProduct nonZeroDivisors in

theorem finrank_int_eq_finrank_ringOfIntegers_mul : ∀ (E : Type) [Field E] [NumberField E] (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.Free ℤ N] [Module.Finite ℤ N], Module.finrank ℤ N = Module.finrank (𝓞 E) N * Module.finrank ℚ E := by
  intro E _ _ N _ _ _ _
  let g : N →ₗ[𝓞 E] E ⊗[𝓞 E] N := TensorProduct.mk (𝓞 E) E N 1
  have hb : IsBaseChange E g := TensorProduct.isBaseChange (𝓞 E) N E
  have h1 : Module.finrank E (E ⊗[𝓞 E] N) = Module.finrank (𝓞 E) N := hb.finrank_eq
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E := inferInstance
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) g :=
    (isLocalizedModule_iff_isBaseChange _ E g).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (g.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars ℤ⁰ g
  have h4 : Module.finrank ℤ (E ⊗[𝓞 E] N) = Module.finrank ℤ N :=
    IsLocalizedModule.finrank_eq ℤ⁰ (g.restrictScalars ℤ) le_rfl
  have h5 : Module.finrank ℚ (E ⊗[𝓞 E] N) = Module.finrank ℤ (E ⊗[𝓞 E] N) :=
    IsFractionRing.finrank_right_eq ℤ ℚ _
  rw [← h4, ← h5, ← h1, mul_comm, Module.finrank_mul_finrank]
end GlobalTheory
