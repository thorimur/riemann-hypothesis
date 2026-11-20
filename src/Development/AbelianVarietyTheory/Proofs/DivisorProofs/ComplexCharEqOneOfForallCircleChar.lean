import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Circle
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
import Mathlib.RingTheory.PiTensorProduct
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

namespace GlobalTheory

noncomputable def circArgChar {G : Type} [Group G] (ν : G →* ℂˣ) : G →* Circle where
  toFun g := ⟨(ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ), by
    have h : ‖(ν g : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν g).ne_zero
    simp [Submonoid.unitSphere, h]⟩
  map_one' := by
    apply Circle.ext
    simp
  map_mul' a b := by
    apply Circle.ext
    show ((ν (a * b) : ℂˣ) : ℂ) / (‖((ν (a * b) : ℂˣ) : ℂ)‖ : ℂ) =
      ((ν a : ℂ) / (‖(ν a : ℂ)‖ : ℂ)) * ((ν b : ℂ) / (‖(ν b : ℂ)‖ : ℂ))
    rw [ν.map_mul, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]

noncomputable def circNormChar {G : Type} [Group G] (ν : G →* ℂˣ) (t : ℝ) : G →* Circle where
  toFun g := Circle.exp (t * Real.log ‖(ν g : ℂ)‖)
  map_one' := by simp
  map_mul' a b := by
    have ha : ‖(ν a : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν a).ne_zero
    have hb : ‖(ν b : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (ν b).ne_zero
    show Circle.exp (t * Real.log ‖((ν (a * b) : ℂˣ) : ℂ)‖) = _
    rw [ν.map_mul, Units.val_mul, norm_mul, Real.log_mul ha hb, mul_add, Circle.exp_add]

private theorem coe_circArgChar_eq_div_norm {G : Type} [Group G] (ν : G →* ℂˣ) (g : G) :
    ((circArgChar ν g : Circle) : ℂ) = (ν g : ℂ) / (‖(ν g : ℂ)‖ : ℂ) := by
  rfl

theorem complexChar_eq_one_of_forall_circleChar :
    ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G),
      (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  intro G _ ν x h
  have hx0 : (ν x : ℂ) ≠ 0 := (ν x).ne_zero
  have hpos : 0 < ‖(ν x : ℂ)‖ := norm_pos_iff.mpr hx0

  have hn : ‖(ν x : ℂ)‖ = 1 := by
    by_contra hne
    have hlog : Real.log ‖(ν x : ℂ)‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hne
    have h2 := h (circNormChar ν (Real.pi / Real.log ‖(ν x : ℂ)‖)) (fun g hg => by
      simp [circNormChar, hg])
    have h3 := congrArg (fun z : Circle => (z : ℂ)) h2
    simp only [circNormChar, MonoidHom.coe_mk, OneHom.coe_mk, Circle.coe_exp,
      div_mul_cancel₀ _ hlog, Circle.coe_one] at h3
    norm_num [Complex.exp_pi_mul_I] at h3

  have h1 := h (circArgChar ν) (fun g hg => by
    apply Circle.ext
    rw [coe_circArgChar_eq_div_norm, hg]
    simp)
  have h4 := congrArg (fun z : Circle => (z : ℂ)) h1
  simp only [coe_circArgChar_eq_div_norm, Circle.coe_one, hn, Complex.ofReal_one, div_one] at h4
  apply Units.ext
  simpa using h4

end GlobalTheory
