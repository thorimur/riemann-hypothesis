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

noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

def twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  C (∏ τ, (emb τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
    bind₁ (fun k : ι × Fin n × Fin n => ∑ j : Fin n,
      C (emb k.1 ((M : Matrix (Fin n) (Fin n) E) k.2.1 j)) * X (k.1, j, k.2.2)) P

def polFun {K ι : Type} [CommRing K] {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) K) :
    (ι → Matrix (Fin n) (Fin n) K) → K :=
  fun y => eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P

theorem polFun_apply {K ι : Type} [CommRing K] {n : ℕ} (P : MvPolynomial (ι × Fin n × Fin n) K)
    (y : ι → Matrix (Fin n) (Fin n) K) : polFun P y = eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) P := rfl

open MvPolynomial in
private lemma eval_bind_eq_eval_comp {K σ τ : Type} [CommRing K] (f : σ → MvPolynomial τ K)
    (x : τ → K) (P : MvPolynomial σ K) :
    eval x (bind₁ f P) = eval (fun i => eval x (f i)) P := by
  rw [← aeval_eq_eval, ← aeval_eq_eval, aeval_bind₁]

open MvPolynomial in
theorem _root_.GlobalTheory.IntegralityCompare.eval_twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (x : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2)
        (_root_.GlobalTheory.IntegralityCompare.twSub emb M s P) =
      (∏ τ, (emb τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
        eval (fun k : ι × Fin n × Fin n =>
          (((M : Matrix (Fin n) (Fin n) E).map (emb k.1)) * x k.1) k.2.1 k.2.2) P := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSub, map_mul, eval_C, eval_bind_eq_eval_comp]
  congr 3
  funext k
  simp [Matrix.mul_apply, eval_sum]

end GlobalTheory.IntegralityCompare

end
