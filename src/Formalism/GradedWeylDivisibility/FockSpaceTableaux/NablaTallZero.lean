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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private lemma isWH_coeff_one_polynomial {r n : ℕ} (δ : ℕ) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ))
      ((1 : Polynomial (MvPolynomial (Fin r × Fin n) ℚ)).coeff k) (0 + k * δ) := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with hk
  · subst hk
    simpa using isWeightedHomogeneous_one (R := ℚ) (w := (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)))
  · exact fun d hd => (hd (coeff_zero d)).elim

private lemma isWH_coeff_mul_of_isWH_coeff {r n : ℕ} (δ : ℕ) (p q : Polynomial (MvPolynomial (Fin r × Fin n) ℚ)) (d e : ℕ)
    (hp : ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) (p.coeff k) (d + k * δ))
    (hq : ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) (q.coeff k) (e + k * δ)) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((p * q).coeff k) (d + e + k * δ) := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have h := (hp x.1).mul (hq x.2)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx]
  convert h using 1
  ring

private lemma isWH_coeff_prod_of_isWH_coeff {r n : ℕ} (δ : ℕ) {ι : Type} (s : Finset ι)
    (p : ι → Polynomial (MvPolynomial (Fin r × Fin n) ℚ)) (d : ι → ℕ)
    (h : ∀ i ∈ s, ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((p i).coeff k) (d i + k * δ)) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((∏ i ∈ s, p i).coeff k) (∑ i ∈ s, d i + k * δ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWH_coeff_one_polynomial (r := r) (n := n) δ
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact isWH_coeff_mul_of_isWH_coeff δ _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Formalism.GradedWeylDivisibility
