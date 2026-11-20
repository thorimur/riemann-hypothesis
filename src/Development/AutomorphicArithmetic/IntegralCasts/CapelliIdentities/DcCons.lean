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
import Mathlib.Tactic.ENatToNat
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

noncomputable def UpperTheory.Reformulated.B.Qj27.dc :
    {Y : Type} → {m : ℕ} → ((Fin (m + (1 : ℕ)) → Y) → ℝ) → (Fin (m + (2 : ℕ)) → Y) → ℝ :=
    fun {Y : Type} {m : ℕ} (F : (Fin (m + (1 : ℕ)) → Y) → ℝ) (y : Fin (m + (2 : ℕ)) → Y) ↦
      ∑ i : Fin (m + (2 : ℕ)), (-1 : ℝ) ^ (↑i : ℕ) * F fun (j : Fin (m + (1 : ℕ))) ↦ y (i.succAbove j)

theorem UpperTheory.Reformulated.B.Qj27.dc_cons :
    ∀ {Y : Type} {m : ℕ} (F : (Fin (m + (2 : ℕ)) → Y) → ℝ) (a : Y) (w : Fin (m + (2 : ℕ)) → Y),
      UpperTheory.Reformulated.B.Qj27.dc F (Fin.cons a w) =
        F w - UpperTheory.Reformulated.B.Qj27.dc (fun (w' : Fin (m + (1 : ℕ)) → Y) ↦ F (Fin.cons a w')) w := by
  intro Y m F a w
  have h : ∀ i : Fin (m + 2),
      (fun j : Fin (m + 2) ↦ (Fin.cons a w : Fin (m + 3) → Y) (i.succ.succAbove j)) =
        (Fin.cons a (fun j : Fin (m + 1) ↦ w (i.succAbove j)) : Fin (m + 2) → Y) := by
    intro i
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp
    · simp
  unfold UpperTheory.Reformulated.B.Qj27.dc
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h i, Fin.val_succ, pow_succ]
    ring
