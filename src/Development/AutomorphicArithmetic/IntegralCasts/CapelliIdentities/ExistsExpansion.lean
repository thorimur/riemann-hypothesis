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
import Mathlib.RingTheory.PiTensorProduct
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

private lemma UpperTheory.Reformulated.B.Qn12.step {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (y c : ι → R) (p e x a : R) (j : ι) (hy : y j = x - a) (hc : p = e + ∑ i, c i * y i) :
    p * x = e * a + ∑ i, (c i * a + if i = j then p else 0) * y i := by
  have h1 : ∑ i, (c i * a + if i = j then p else 0) * y i = (∑ i, c i * y i) * a + p * y j := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Finset.sum_mul, mul_right_comm]
  rw [h1, hy]
  linear_combination a * hc

private lemma UpperTheory.Reformulated.B.Qn12.step_add {R ι : Type*} [CommRing R] [Fintype ι]
    (y c d : ι → R) (p r e f : R) (hc : p = e + ∑ i, c i * y i) (hd : r = f + ∑ i, d i * y i) :
    p + r = (e + f) + ∑ i, (c i + d i) * y i := by
  simp only [add_mul, Finset.sum_add_distrib]
  linear_combination hc + hd

theorem UpperTheory.Reformulated.B.Qn12.exists_expansion :
    ∀ {n : ℕ} (q : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℂ),
    ∃ (c : Fin n → MvPolynomial (Fin n) ℂ),
      p =
        (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) ((MvPolynomial.eval q : MvPolynomial (Fin n) ℂ → ℂ) p) +
          ∑ i : Fin n, c i * (MvPolynomial.X i - (MvPolynomial.C : ℂ → MvPolynomial (Fin n) ℂ) (q i)) := by
  intro n q p
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, by simp⟩
  | add p r hp hr =>
    obtain ⟨c, hc⟩ := hp
    obtain ⟨d, hd⟩ := hr
    refine ⟨fun i => c i + d i, ?_⟩
    rw [map_add, map_add]
    exact UpperTheory.Reformulated.B.Qn12.step_add _ c d p r _ _ hc hd
  | mul_X p j hp =>
    obtain ⟨c, hc⟩ := hp
    refine ⟨fun i => c i * MvPolynomial.C (q j) + if i = j then p else 0, ?_⟩
    rw [map_mul, MvPolynomial.eval_X, map_mul]
    exact UpperTheory.Reformulated.B.Qn12.step (fun i => MvPolynomial.X i - MvPolynomial.C (q i)) c p _ _ _ j rfl hc
