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
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem mvPowerSeries_three_eq_zero_of_subst_lines :
    ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K),
      (∀ t : Fin 3 → K, (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) →
      Φ = 0 := by
  intro K _ _ Φ h
  ext d
  set n := ∑ i, d i with hn
  let S : Finset (Fin 3 →₀ ℕ) :=
    (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => n)).filter (fun e => ∑ i, e i = n)
  have hS : ∀ e, e ∈ S ↔ ∑ i, e i = n := by
    intro e
    simp only [S, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
    intro he i
    change e i ≤ n
    rw [← he]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  let P : MvPolynomial (Fin 3) K := ∑ e ∈ S, MvPolynomial.monomial e (MvPowerSeries.coeff e Φ)
  have hcoef : ∀ t : Fin 3 → K, PowerSeries.coeff n (MvPowerSeries.subst
      (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) = MvPolynomial.eval t P := by
    intro t
    have ha : MvPowerSeries.HasSubst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
        rw [map_mul]; exact mul_eq_zero_of_right _ (MvPowerSeries.constantCoeff_X ()))
    have hprod : ∀ e : Fin 3 →₀ ℕ,
        (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) =
          PowerSeries.C (∏ s, t s ^ e s) * PowerSeries.X ^ (∑ s, e s) := by
      intro e
      rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
    have h1 : PowerSeries.coeff n (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) =
        ∑ᶠ e : Fin 3 →₀ ℕ, MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) :=
      MvPowerSeries.coeff_subst ha Φ (Finsupp.single () n)
    rw [h1]
    simp only [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul]
    rw [finsum_eq_sum_of_support_subset _ (s := S) ?_]
    · simp only [P, map_sum, MvPolynomial.eval_monomial]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [if_pos ((hS e).1 he).symm, Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
    · intro e he
      rw [Function.mem_support] at he
      rw [Finset.mem_coe, hS]
      by_contra hne
      exact he (by rw [if_neg (Ne.symm hne), mul_zero])
  have hP : P = 0 := MvPolynomial.funext (fun t => by rw [← hcoef, h t, map_zero, map_zero])
  have hd := congrArg (MvPolynomial.coeff d) hP
  simp only [P, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hS d).2 rfl)] at hd
  simpa using hd

end GlobalTheory
