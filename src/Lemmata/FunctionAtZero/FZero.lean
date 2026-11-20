import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Sheaves.Init

namespace Bl.FunctionAtZero

private lemma f_zero (f : Real → Complex) (hmul : ∀ s t, f (s + t) = f s * f t)
    (hn : ∀ s, ‖f s‖ = 1) : f 0 = 1 := by
  have h := hmul 0 0
  rw [add_zero] at h
  have h0 : f 0 ≠ 0 := by
    intro h'
    have := hn 0
    rw [h', norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ h0 (h.symm.trans (mul_one (f 0)).symm)

theorem goal1 :
  ∀ (f : Real → Complex),
  Continuous.{0, 0} f →
    (∀ (s t : Real), Eq.{1} (f (HAdd.hAdd.{0, 0, 0} s t)) (HMul.hMul.{0, 0, 0} (f s) (f t))) →
      (∀ (s : Real), Eq.{1} (Norm.norm.{0} (f s)) 1) →
        Exists.{1} fun (b : Real) ↦
          ∀ (s : Real),
            Eq.{1} (f s) (Complex.exp (HMul.hMul.{0, 0, 0} (Complex.ofReal (HMul.hMul.{0, 0, 0} b s)) Complex.I)) := by
  intro f hf hmul hn
  have h0 := f_zero f hmul hn
  let F : C(Real, Circle) := ⟨fun s => ⟨f s, mem_sphere_zero_iff_norm.2 (hn s)⟩, hf.subtype_mk _⟩
  have hF : ∀ s, ((F s : Circle) : Complex) = f s := fun s => rfl
  obtain ⟨g, ⟨hg0, hgF⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts F 0 0
    (Circle.ext (by rw [Circle.coe_exp, hF, h0]; simp))
  have key : ∀ s, Complex.exp (↑(g s) * Complex.I) = f s := fun s => by
    rw [← Circle.coe_exp, ← hF]
    exact congrArg (fun z : Circle => (z : Complex)) (congrFun hgF s)
  have hadd : ∀ s t, g (s + t) = g s + g t := by
    intro s t
    have := Circle.isCoveringMap_exp.eq_of_comp_eq (g₁ := fun s => g (s + t))
      (g₂ := fun s => g s + g t)
      (g.continuous.comp (continuous_id.add continuous_const)) (g.continuous.add continuous_const)
      (by
        funext x
        apply Circle.ext
        simp only [Function.comp_apply, Circle.coe_exp, Complex.ofReal_add, add_mul,
          Complex.exp_add, key, hmul]) 0 (by simp [hg0])
    exact congrFun this s
  let G : Real →+ Real := AddMonoidHom.mk' g hadd
  have hlin : ∀ s, g s = s * g 1 := by
    intro s
    have := map_real_smul G (by exact g.continuous) s 1
    simpa [G] using this
  refine ⟨g 1, fun s => ?_⟩
  rw [← key s, hlin s, mul_comm s]

end Bl.FunctionAtZero
