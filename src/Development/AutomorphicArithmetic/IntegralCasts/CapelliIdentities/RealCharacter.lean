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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.Reformulated.B.UnitaryCharacterOfReals.char_real :
    ∀ (f : ℝ → ℂ),
    Continuous f →
      (∀ (s t : ℝ), f (s + t) = f s * f t) →
        (∀ (s : ℝ), ‖f s‖ = (1 : ℝ)) → ∃ (b : ℝ), ∀ (s : ℝ), f s = Complex.exp ((↑(b * s) : ℂ) * Complex.I) := by
  intro f hf hadd hn
  let F : C(ℝ, Circle) :=
    ⟨fun s => ⟨f s, mem_sphere_zero_iff_norm.2 (hn s)⟩, hf.subtype_mk _⟩
  have hF : ∀ s, (F s : ℂ) = f s := fun _ => rfl
  have hFadd : ∀ s t, F (s + t) = F s * F t := fun s t => by
    apply Circle.ext
    rw [Circle.coe_mul, hF, hF, hF, hadd]
  have hF0 : F 0 = 1 := by
    have h := hFadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have cov := Circle.isCoveringMap_exp
  obtain ⟨g, ⟨hg0, hg⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts F 0 0 (by rw [hF0]; exact Circle.exp_zero)
  have hg' : ∀ s, Circle.exp (g s) = F s := fun s => congrFun hg s
  have gadd : ∀ s t, g (s + t) = g s + g t := fun s t => by
    have h := cov.eq_of_comp_eq (g₁ := fun s : ℝ => g (s + t)) (g₂ := fun s : ℝ => g s + g t)
      (by fun_prop) (by fun_prop)
      (by
        funext s
        show Circle.exp (g (s + t)) = Circle.exp (g s + g t)
        rw [Circle.exp_add, hg', hg', hg', hFadd]) 0 (by simp [hg0])
    exact congrFun h s
  let G : ℝ →+ ℝ := AddMonoidHom.mk' g gadd
  refine ⟨g 1, fun s => ?_⟩
  have hs : g s = g 1 * s := by
    have h := map_real_smul G g.continuous s 1
    simp only [smul_eq_mul, mul_one] at h
    rw [mul_comm]
    exact h
  rw [← hs, ← hF, ← hg', Circle.coe_exp]
