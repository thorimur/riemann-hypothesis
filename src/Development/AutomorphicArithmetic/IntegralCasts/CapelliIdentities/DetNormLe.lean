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

noncomputable def UpperTheory.Reformulated.B.Qi39.EB.{u_1, u_2} :
    {m : Type u_1} → {n : Type u_2} → Matrix m n ℂ → ℝ → Prop :=
    fun {m : Type u_1} {n : Type u_2} (A : Matrix m n ℂ) (c : ℝ) ↦ ∀ (i : m) (j : n), ‖A i j‖ ≤ c

theorem UpperTheory.Reformulated.B.Qi39.det_norm_le.{u_1} :
    ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] (A : Matrix n n ℂ) {m : ℝ},
      UpperTheory.Reformulated.B.Qi39.EB A m → ‖A.det‖ ≤ (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by
  intro n _ _ A m h
  have hterm : ∀ σ : Equiv.Perm n,
      ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ m ^ Fintype.card n := by
    intro σ
    have hs : ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ = ‖∏ i, A (σ i) i‖ := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · rw [h1, one_smul]
      · rw [h1, Units.neg_smul, one_smul, norm_neg]
    rw [hs, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : n, m :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h (σ i) i)
      _ = m ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm n, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm n, m ^ Fintype.card n := Finset.sum_le_sum fun σ _ => hterm σ
    _ = (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
