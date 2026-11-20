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

noncomputable def UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR :
    {K : Type} → [inst : CommRing K] → Subring K → (n : ℕ) → Subgroup (GL (Fin n) K) :=
  fun {K} _ R n =>
  { carrier := {g | (∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ R) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ R}
    one_mem' := by
      have h : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) K) i j ∈ R := fun i j => by
        rw [Matrix.one_apply]
        split_ifs
        exacts [R.one_mem, R.zero_mem]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_one]
        exact h i j
      · rw [inv_one, Units.val_one]
        exact h i j
    mul_mem' := by
      rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (ha i k) (hb k j)
      · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (hb' i k) (ha' k j)
    inv_mem' := by
      rintro a ⟨ha, ha'⟩
      refine ⟨ha', fun i j => ?_⟩
      rw [inv_inv]
      exact ha i j }
