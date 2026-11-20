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
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace PI.OrbShared

open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

variable {σ τ υ R : Type*} [CommRing R]

theorem hasSubst_killCompl (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a) :
    HasSubst (fun s => killCompl e (a s)) where
  const_coeff s := by
    have h : constantCoeff (killCompl e (a s)) = constantCoeff (a s) := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
        coeff_killCompl, Finsupp.embDomain_zero]
    rw [h]; exact ha.const_coeff s
  coeff_zero d := by
    refine (ha.coeff_zero (Finsupp.embDomain e d)).subset ?_
    intro s hs
    simpa [coeff_killCompl] using hs

theorem continuous_killCompl [UniformSpace R] [DiscreteUniformity R] (e : υ ↪ τ) :
    Continuous (killCompl (R := R) e : MvPowerSeries τ R → MvPowerSeries υ R) := by
  apply continuous_pi
  intro x
  have : (fun p : MvPowerSeries τ R => (killCompl e p) x) = fun p => coeff (Finsupp.embDomain e x) p := by
    funext p; exact coeff_killCompl p x
  rw [this]
  exact WithPiTopology.continuous_coeff R _

theorem killCompl_subst (e : υ ↪ τ) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (f : MvPowerSeries σ R) :
    killCompl e (subst a f) = subst (fun s => killCompl e (a s)) f := by
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hb := hasSubst_killCompl e ha
  rw [comp_subst_apply ha (continuous_killCompl e) f, ← coe_substAlgHom hb, substAlgHom_eq_aeval]

theorem killCompl_eq_subst (e : υ ↪ τ) (f : MvPowerSeries τ R) :
    killCompl e f = subst (fun t => killCompl e (X t : MvPowerSeries τ R)) f := by
  have := killCompl_subst e (HasSubst.X (S := R) (σ := τ)) f
  rw [subst_self] at this
  exact this

end PI.OrbShared
