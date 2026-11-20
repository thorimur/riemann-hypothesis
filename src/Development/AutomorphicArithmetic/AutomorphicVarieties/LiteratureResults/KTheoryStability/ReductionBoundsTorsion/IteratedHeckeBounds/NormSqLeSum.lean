import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.JoinReconstruction

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def sx (q : ℕ) : Set (Fin q → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

def pt {q : ℕ} (y : Fin (q + 1) → V) (t : Fin q → ℝ) : V := y 0 + ∑ j, t j • (y j.succ - y 0)

theorem recon [FiniteDimensional ℝ V] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (b : Module.Basis κ ℝ V) :
    ∃ Ψ : ((ι → κ) → ℝ) →L[ℝ] (V [⋀^ι]→L[ℝ] ℝ), ∀ A : V [⋀^ι]→L[ℝ] ℝ, Ψ (fun v => A fun i => b (v i)) = A := by
  let L : (V [⋀^ι]→L[ℝ] ℝ) →ₗ[ℝ] ((ι → κ) → ℝ) :=
    { toFun := fun A v => A fun i => b (v i)
      map_add' := fun A B => by
        ext v
        simp
      map_smul' := fun c A => by
        ext v
        simp }
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    have hm : A.toMultilinearMap = (0 : V [⋀^ι]→L[ℝ] ℝ).toMultilinearMap := by
      refine Module.Basis.ext_multilinear (fun _ => b) fun v => ?_
      have := congrFun hA v
      simpa [L] using this
    ext x
    simpa using congrFun (congrArg DFunLike.coe hm) x
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective L hL
  refine ⟨LinearMap.toContinuousLinearMap g, fun A => ?_⟩
  have := congrArg (fun f => f A) hg
  simpa [L] using this

theorem norm_sq_le_sum {κ : Type} [Fintype κ] (u : κ → ℝ) : ‖u‖ ^ 2 ≤ ∑ v, u v ^ 2 := by
  have hs : 0 ≤ ∑ v, u v ^ 2 := Finset.sum_nonneg fun v _ => sq_nonneg _
  have h : ‖u‖ ≤ Real.sqrt (∑ v, u v ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun w => u w ^ 2) (fun w _ => sq_nonneg (u w)) (Finset.mem_univ v))
  calc ‖u‖ ^ 2 ≤ Real.sqrt (∑ v, u v ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ v, u v ^ 2 := Real.sq_sqrt hs

end PositivityTheory.KB.JoinReconstruction

end
