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
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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

open NumberField IsDedekindDomain

namespace GlobalTheory.StdAtPrime

variable {E : Type} [Field E] [NumberField E]

def Bnd (p : ℕ) {n : ℕ} (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Prop :=
  ∃ m : ℕ, m.Coprime p ∧ ∀ (i j : Fin n) (Q : HeightOneSpectrum (𝓞 E)),
    Valued.v ((((m : FiniteAdeleRing (𝓞 E) E) * A i j)) Q) ≤ 1

theorem bnd_mul (p n : ℕ) (A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hA : Bnd p A) (hB : Bnd p B) :
    Bnd p (A * B) := by
  obtain ⟨a, ha, hA⟩ := hA
  obtain ⟨b, hb, hB⟩ := hB
  refine ⟨a * b, Nat.Coprime.mul_left ha hb, fun i j Q => ?_⟩
  let φ : FiniteAdeleRing (𝓞 E) E →+* _ := RestrictedProduct.evalRingHom _ Q
  have hφ : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = φ x := fun _ => rfl
  rw [hφ, Matrix.mul_apply, Finset.mul_sum, map_sum]
  apply Valuation.map_sum_le
  intro k _
  have hsplit : ((a * b : ℕ) : FiniteAdeleRing (𝓞 E) E) * (A i k * B k j) =
      ((a : FiniteAdeleRing (𝓞 E) E) * A i k) * ((b : FiniteAdeleRing (𝓞 E) E) * B k j) := by
    push_cast; ring
  rw [hsplit, map_mul, Valuation.map_mul, ← hφ, ← hφ]
  exact mul_le_one' (hA i k Q) (hB k j Q)

end GlobalTheory.StdAtPrime
