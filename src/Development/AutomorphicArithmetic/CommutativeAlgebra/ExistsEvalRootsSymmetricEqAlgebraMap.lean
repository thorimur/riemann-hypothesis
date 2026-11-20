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
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

noncomputable section
open Polynomial

theorem UpperTheory.exists_eval_roots_symmetric_eq_algebraMap :
    ∀ (A : Type) [CommRing A] (N : ℕ) (g : A[X]) (F : MvPolynomial (Fin N) A), F.IsSymmetric → ∃ a : A, ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) → MvPolynomial.aeval x F = algebraMap A S a := by
  intro A _ N g F hF
  obtain ⟨P, hP⟩ := MvPolynomial.esymmAlgHom_fin_surjective A (le_refl N) ⟨F, hF⟩
  have hPF : MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A (i + 1)) P = F := by
    rw [← MvPolynomial.esymmAlgHom_apply, hP]
  let c : Fin N → A := fun i => (-1) ^ ((i : ℕ) + 1) * g.coeff (N - ((i : ℕ) + 1))
  refine ⟨MvPolynomial.aeval c P, ?_⟩
  intro S _ _ x hg
  have key : ∀ i : Fin N, MvPolynomial.aeval x (MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1)) =
      algebraMap A S (c i) := by
    intro i
    have hi := i.2
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
    set s := Finset.univ.val.map x with hs
    have hcs : Multiset.card s = N := by simp [s]
    have hprod : (s.map fun t => X - C t).prod = g.map (algebraMap A S) := by
      rw [hg, Finset.prod_eq_multiset_prod, hs, Multiset.map_map]
      rfl
    have hk : N - ((i : ℕ) + 1) ≤ Multiset.card s := by omega
    have hco := Multiset.prod_X_sub_C_coeff s hk
    rw [hprod, Polynomial.coeff_map, hcs, show N - (N - ((i : ℕ) + 1)) = (i : ℕ) + 1 by omega]
      at hco
    simp only [c, map_mul, map_pow, map_neg, map_one, hco]
    rw [← mul_assoc, ← mul_pow]
    simp
  have hcomp : (MvPolynomial.aeval x).comp
      (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1))) =
      MvPolynomial.aeval (fun i => algebraMap A S (c i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.aeval_X, key]
  calc MvPolynomial.aeval x F
      = ((MvPolynomial.aeval x).comp
          (MvPolynomial.aeval (fun i : Fin N => MvPolynomial.esymm (Fin N) A ((i : ℕ) + 1)))) P := by
        rw [← hPF]
        rfl
    _ = MvPolynomial.aeval (fun i => algebraMap A S (c i)) P := by rw [hcomp]
    _ = algebraMap A S (MvPolynomial.aeval c P) := MvPolynomial.aeval_algebraMap_apply S c P

end
