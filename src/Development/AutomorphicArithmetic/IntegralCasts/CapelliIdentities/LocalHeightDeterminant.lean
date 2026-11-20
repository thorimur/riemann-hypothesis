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
import Mathlib.Topology.Sheaves.Presheaf

noncomputable def UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight.{u_1} :
    {E : Type u_1} → [inst : NormedField E] → {n : ℕ} → GL (Fin n) E → ℝ :=
    fun {E : Type u_1} [NormedField E] {n : ℕ} (g : GL (Fin n) E) ↦
      Max.max (1 : ℝ)
        (↑(Finset.univ.sup fun (p : Fin n × Fin n) ↦
              Max.max ‖(↑g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊ ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) :
          ℝ)

theorem UpperTheory.Reformulated.B.LocalHeightDeterminant.norm_det_le_pow.{u_1} :
    ∀ {R : Type u_1} [inst : NormedField R] [IsUltrametricDist R] {n : ℕ} (g : GL (Fin n) R),
      ‖(↑g : Matrix (Fin n) (Fin n) R).det‖ ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g ^ n := by
  intro R _ _ n g
  have h1 : (1 : ℝ) ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := le_max_left _ _
  have h0 : (0 : ℝ) ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := zero_le_one.trans h1
  have hent : ∀ i j, ‖(↑g : Matrix (Fin n) (Fin n) R) i j‖ ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := by
    intro i j
    refine le_trans ?_ (le_max_right _ _)
    rw [← coe_nnnorm, NNReal.coe_le_coe]
    exact (le_max_left _ _).trans (Finset.le_sup (f := fun (p : Fin n × Fin n) ↦
      Max.max ‖(↑g : Matrix (Fin n) (Fin n) R) p.1 p.2‖₊
        ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) R) p.1 p.2‖₊) (Finset.mem_univ (i, j)))
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg h0 n) ?_
  intro σ _
  have hs : ‖Equiv.Perm.sign σ • ∏ i, (↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖
      = ‖∏ i, (↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, norm_prod]
  calc ∏ i, ‖(↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖
      ≤ ∏ _i : Fin n, UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g :=
        Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hent _ _)
    _ = UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g ^ n := by simp
