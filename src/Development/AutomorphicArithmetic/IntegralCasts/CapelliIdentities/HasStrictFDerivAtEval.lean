import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.Qi29.polyDeriv :
    {n : ℕ} → MvPolynomial (Fin n) ℂ → EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    fun {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) ↦
      ∑ l : Fin n,
        (MvPolynomial.eval fun (i : Fin n) ↦ x.ofLp i : MvPolynomial (Fin n) ℂ → ℂ)
            ((MvPolynomial.pderiv l : MvPolynomial (Fin n) ℂ → MvPolynomial (Fin n) ℂ) p) •
          EuclideanSpace.proj l

theorem UpperTheory.Reformulated.B.Qi29.hasStrictFDerivAt_eval :
    ∀ {n : ℕ} (p : MvPolynomial (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)),
      HasStrictFDerivAt
        (fun (y : EuclideanSpace ℂ (Fin n)) ↦ (MvPolynomial.eval fun (i : Fin n) ↦ y.ofLp i : MvPolynomial (Fin n) ℂ → ℂ) p)
        (UpperTheory.Reformulated.B.Qi29.polyDeriv p x) x := by
  intro n p x
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (MvPolynomial.C a : MvPolynomial (Fin n) ℂ) x = 0 := by
      simp [UpperTheory.Reformulated.B.Qi29.polyDeriv]
    rw [h]
    simp only [MvPolynomial.eval_C]
    exact hasStrictFDerivAt_const a x
  | add p q hp hq =>
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p + q) x
        = UpperTheory.Reformulated.B.Qi29.polyDeriv p x + UpperTheory.Reformulated.B.Qi29.polyDeriv q x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, map_add, add_smul, Finset.sum_add_distrib]
    rw [h]
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : HasStrictFDerivAt (fun y : EuclideanSpace ℂ (Fin n) ↦ y.ofLp i)
        (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) x :=
      (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).hasStrictFDerivAt
    have h : UpperTheory.Reformulated.B.Qi29.polyDeriv (p * MvPolynomial.X i) x
        = (MvPolynomial.eval (fun j : Fin n ↦ x.ofLp j) p) •
            (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
          + (x.ofLp i) • UpperTheory.Reformulated.B.Qi29.polyDeriv p x := by
      simp only [UpperTheory.Reformulated.B.Qi29.polyDeriv, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        MvPolynomial.eval_X, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [MvPolynomial.pderiv_X_of_ne hb.symm]
      · simp
    rw [h]
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul hi
