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
import Mathlib.NumberTheory.JacobiSum.Basic
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
import Mathlib.Topology.Sheaves.Init

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

theorem UpperTheory.V.Stick.jacDvd :
    ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (p : ℕ) [Fact p.Prime] (χ φ : MulChar (ZMod p) R),
    χ ≠ 1 → φ ≠ 1 → χ * φ ≠ 1 → jacobiSum χ φ ∣ (p : R) := by
  intro R _ _ _ p _ χ φ hχ hφ hχφ
  let K := FractionRing R
  let f : R →+* K := algebraMap R K
  have hf : Function.Injective f := IsFractionRing.injective R K
  have : CharZero K := charZero_of_injective_algebraMap hf
  have hc : ringChar K ≠ ringChar (ZMod p) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact (Fact.out : p.Prime).ne_zero.symm
  have h1 : χ.ringHomComp f ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).mpr hχ
  have h2 : φ.ringHomComp f ≠ 1 := (MulChar.ringHomComp_ne_one_iff hf).mpr hφ
  have h3 : χ.ringHomComp f * φ.ringHomComp f ≠ 1 := by
    rw [← MulChar.ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hf).mpr hχφ
  have key := jacobiSum_mul_jacobiSum_inv hc h1 h2 h3
  rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_inv, jacobiSum_ringHomComp,
    jacobiSum_ringHomComp, ← map_mul, ZMod.card, ← map_natCast f] at key
  exact ⟨_, (hf key).symm⟩
