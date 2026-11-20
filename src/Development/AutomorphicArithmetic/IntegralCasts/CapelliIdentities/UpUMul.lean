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

noncomputable def UpperTheory.Reformulated.B.Qh21.UpU.{u_1} :
    {K : Type u_1} → [Field K] → {N : ℕ} → Matrix (Fin N) (Fin N) K → Prop :=
    fun {K : Type u_1} [Field K] {N : ℕ} (U : Matrix (Fin N) (Fin N) K) ↦
      ∀ (i j : Fin N), (j < i → U i j = (0 : K)) ∧ (i = j → U i j = (1 : K))

theorem UpperTheory.Reformulated.B.Qh21.upU_mul.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] {N : ℕ} {A B : Matrix (Fin N) (Fin N) K},
      UpperTheory.Reformulated.B.Qh21.UpU A → UpperTheory.Reformulated.B.Qh21.UpU B → UpperTheory.Reformulated.B.Qh21.UpU (A * B) := by
  intro K _ N A B hA hB i j
  have hz : j ≤ i → ∀ k : Fin N, k ≠ i → A i k * B k j = 0 := by
    intro hji k hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [(hA i k).1 h, zero_mul]
    · rw [(hB k j).1 (lt_of_le_of_lt hji h), mul_zero]
  have hs : j ≤ i → (A * B) i j = B i j := by
    intro hji
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => hz hji k hk)
      (fun h => absurd (Finset.mem_univ i) h), (hA i i).2 rfl, one_mul]
  exact ⟨fun h => (hs h.le).trans ((hB i j).1 h), fun h => (hs h.ge).trans ((hB i j).2 h)⟩
