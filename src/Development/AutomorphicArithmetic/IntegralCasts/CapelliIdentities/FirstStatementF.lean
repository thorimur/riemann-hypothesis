import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.NumberTheory.Padics.Complex
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

theorem UpperTheory.Reformulated.B.PadicComplexProdXSubCCoeffNorm.aux1 :
    ∀ (p : Nat.Primes), Fact (Nat.Prime (↑p : ℕ)) := by
  intro p
  exact ⟨p.2⟩

attribute [local instance] UpperTheory.Reformulated.B.PadicComplexProdXSubCCoeffNorm.aux1

theorem UpperTheory.Reformulated.B.PadicComplexProdXSubCCoeffNorm.main :
    ∀ {p : Nat.Primes} (s : Multiset ℂ_[(↑p : ℕ)]),
      (∀ r ∈ s, ‖r‖ ≤ (1 : ℝ)) →
        ∀ (i : ℕ),
          ‖(Multiset.map (fun (r : ℂ_[(↑p : ℕ)]) ↦ Polynomial.X - (Polynomial.C : ℂ_[(↑p : ℕ)] → Polynomial ℂ_[(↑p : ℕ)]) r)
                      s).prod.coeff
                i‖ ≤
            (1 : ℝ) := by
  intro p s
  induction s using Multiset.induction_on with
  | empty =>
    intro _ i
    simp only [Multiset.map_zero, Multiset.prod_zero, Polynomial.coeff_one]
    split_ifs <;> simp
  | cons a s ih =>
    intro h i
    have ha : ‖a‖ ≤ 1 := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun r hr => h r (Multiset.mem_cons_of_mem hr))
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul]
    have h2 : ‖a * (Multiset.map (fun r => Polynomial.X - Polynomial.C r) s).prod.coeff i‖ ≤ 1 := by
      rw [norm_mul]
      exact mul_le_one₀ ha (norm_nonneg _) (hs i)
    have h1 : ‖(Polynomial.X * (Multiset.map (fun r => Polynomial.X - Polynomial.C r) s).prod).coeff i‖ ≤ 1 := by
      cases i with
      | zero => simp
      | succ n => rw [Polynomial.coeff_X_mul]; exact hs n
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
