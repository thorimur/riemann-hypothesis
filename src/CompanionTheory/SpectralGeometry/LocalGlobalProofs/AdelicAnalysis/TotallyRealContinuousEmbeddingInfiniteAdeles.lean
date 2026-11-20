import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
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

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicRealLine

theorem norm_eq_abs_ringEquiv {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (x : w.Completion) :
    ‖x‖ = |InfinitePlace.Completion.ringEquivRealOfIsReal hw x| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).dist_eq x 0
  have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hw) 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  rw [h0, dist_zero_right, dist_zero_right] at h
  rw [← h, Real.norm_eq_abs]
  rfl

theorem exists_continuous_real_embedding :
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
      (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧
        ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
          ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  intro F _ _ hF
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => @IsTotallyReal.isReal F _ hF w
  refine ⟨⟨Pi.ringHom fun w =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).symm.toRingHom, ?_⟩, ?_⟩
  · refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm.continuous
  · intro θ _ t w
    have hφ := DFunLike.congr_fun (Subsingleton.elim
      (((InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).toRingHom.comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) : ℝ →+* ℝ)
      (RingHom.id ℝ)) t
    change InfinitePlace.Completion.ringEquivRealOfIsReal (hr w) (θ t w) = t at hφ
    rw [GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv (hr w), hφ]

end GlobalTheory.CompanionTheory.AdelicRealLine
