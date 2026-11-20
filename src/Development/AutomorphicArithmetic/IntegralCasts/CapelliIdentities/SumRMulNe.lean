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

theorem UpperTheory.Reformulated.B.Qn10.sum_r_mul_ne.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A]
    {n : ℕ} (f : MvPolynomial (Fin (n + (1 : ℕ))) A) (v w : Fin (n + (1 : ℕ)) →₀ ℕ),
    (∀ (i : Fin (n + (1 : ℕ))), (v : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
      (∀ (i : Fin (n + (1 : ℕ))), (w : Fin (n + (1 : ℕ)) → ℕ) i < (2 : ℕ) + f.totalDegree) →
        v ≠ w →
          ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (v : Fin (n + (1 : ℕ)) → ℕ) x ≠
            ∑ x : Fin (n + (1 : ℕ)),
              (fun (i : Fin (n + (1 : ℕ))) ↦ ((2 : ℕ) + f.totalDegree) ^ (↑i : ℕ)) x * (w : Fin (n + (1 : ℕ)) → ℕ) x := by
  intro A _ _ n f v w hv hw hne h
  apply hne
  have key : finFunctionFinEquiv (fun i => (⟨v i, hv i⟩ : Fin (2 + f.totalDegree))) =
      finFunctionFinEquiv (fun i => (⟨w i, hw i⟩ : Fin (2 + f.totalDegree))) := by
    apply Fin.ext
    rw [finFunctionFinEquiv_apply, finFunctionFinEquiv_apply]
    simpa only [mul_comm] using h
  have hfun := finFunctionFinEquiv.injective key
  ext i
  exact congrArg Fin.val (congrFun hfun i)
