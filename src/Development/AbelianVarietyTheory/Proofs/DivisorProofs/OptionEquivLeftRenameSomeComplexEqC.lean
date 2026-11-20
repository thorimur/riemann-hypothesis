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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
open MvPolynomial

namespace GlobalTheory

theorem optionEquivLeft_rename_some_complex_eq_C {τ : Type} (c : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.rename some c) = Polynomial.C c := by
  induction c using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_C, Polynomial.C_eq_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.C_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, MvPolynomial.rename_X, MvPolynomial.optionEquivLeft_X_some, Polynomial.C_mul]

theorem coeff_optionEquivLeft_extDerivation {τ : Type}
    (E : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ)) (k : ℕ) (s : MvPolynomial (Option τ) ℂ) :
    (MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.mkDerivation ℂ (fun w : Option τ => match w with
      | none => (0 : MvPolynomial (Option τ) ℂ)
      | some v => MvPolynomial.rename some (E (MvPolynomial.X v))) s)).coeff k
      = E ((MvPolynomial.optionEquivLeft ℂ τ (s)).coeff k) := by
  induction s using MvPolynomial.induction_on generalizing k with
  | C a =>
    have h1 : (MvPolynomial.C a : MvPolynomial (Option τ) ℂ) = algebraMap ℂ _ a := rfl
    have h2 : (MvPolynomial.C a : MvPolynomial τ ℂ) = algebraMap ℂ _ a := rfl
    rw [h1, Derivation.map_algebraMap, ← h1, MvPolynomial.optionEquivLeft_C, Polynomial.coeff_C]
    split_ifs <;> simp [h2, Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p n hp =>
    rw [Derivation.leibniz, MvPolynomial.mkDerivation_X]
    rcases n with _ | v
    · simp only [smul_zero, zero_add, smul_eq_mul, mul_zero, map_mul, MvPolynomial.optionEquivLeft_X_none]
      rcases k with _ | k
      · simp [Polynomial.coeff_mul_X_zero, mul_comm (Polynomial.X) _]
      · rw [mul_comm Polynomial.X, Polynomial.coeff_mul_X, Polynomial.coeff_mul_X, hp]
    · simp only [smul_eq_mul, map_add, map_mul, MvPolynomial.optionEquivLeft_X_some, optionEquivLeft_rename_some_complex_eq_C,
        Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, hp, Derivation.leibniz]

end GlobalTheory
