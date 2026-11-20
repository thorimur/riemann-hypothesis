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

open MeasureTheory Set

noncomputable section

namespace Formalism.MainNotions.S.Gauge

theorem mp_uncurry (κ : Type*) [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry κ (Fin 2) ℝ).symm volume volume := by
  refine ⟨(MeasurableEquiv.curry κ (Fin 2) ℝ).symm.measurable, ?_⟩
  refine (Measure.pi_eq (fun s _ => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : ((MeasurableEquiv.curry κ (Fin 2) ℝ).symm) ⁻¹' (univ.pi s) =
      univ.pi (fun k => univ.pi (fun i => s (k, i))) := by
    ext x; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
  rw [hpre, volume_pi_pi]
  simp_rw [volume_pi_pi]
  rw [Fintype.prod_prod_type]

theorem mp_cF (κ : Type*) [Fintype κ] :
    MeasurePreserving (fun y : EuclideanSpace ℝ (κ × Fin 2) => fun k => (y (k, 0) : ℂ) + (y (k, 1) : ℂ) * Complex.I)
      volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (ι := κ × Fin 2)
  have h2 := MeasurePreserving.symm _ (mp_uncurry κ)
  have h3 := volume_preserving_pi (fun _ : κ => Complex.volume_preserving_equiv_pi.symm)
  exact (h3.comp h2).comp h1

end Formalism.MainNotions.S.Gauge
