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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

universe u_1

namespace Bl.FirstBlockLemmaJ

theorem goal1 :
  ∀ {V : Type u_1} [inst : NormedAddCommGroup.{u_1} V] [inst_1 : NormedSpace.{0, u_1} Complex V] {g : V → Complex} {x : V}
  {ε : Real},
  DifferentiableOn.{0, u_1, 0} Complex g (Metric.ball.{u_1} x ε) →
    ∀ {z : V},
      Membership.mem.{u_1, u_1} (Metric.ball.{u_1} x ε) z →
        Filter.EventuallyEq.{u_1, 0} (nhds.{u_1} z) g 0 →
          ∀ (y : V), Membership.mem.{u_1, u_1} (Metric.ball.{u_1} x ε) y → Eq.{1} (g y) 0 := by
  intro V _ _ g x ε hg z hz hz0 y hy
  let φ : ℂ → V := fun t => z + t • (y - z)
  have hφd : Differentiable ℂ φ := (differentiable_const z).add (differentiable_id.smul_const (y - z))
  have hφc : Continuous φ := hφd.continuous
  let U : Set ℂ := φ ⁻¹' Metric.ball x ε
  have hUo : IsOpen U := Metric.isOpen_ball.preimage hφc
  have hdiff : DifferentiableOn ℂ (g ∘ φ) U := hg.comp hφd.differentiableOn (fun t ht => ht)
  have han : AnalyticOnNhd ℂ (g ∘ φ) U := hdiff.analyticOnNhd hUo
  let S : Set ℂ := (fun θ : ℝ => (θ : ℂ)) '' Set.Icc (0 : ℝ) 1
  have hSc : IsPreconnected S := isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
  have hSU : S ⊆ U := by
    rintro t ⟨θ, hθ, rfl⟩
    show z + (θ : ℂ) • (y - z) ∈ Metric.ball x ε
    rw [Complex.coe_smul]
    exact (convex_ball x ε).add_smul_sub_mem hz hy hθ
  have h0 : (0 : ℂ) ∈ S := ⟨0, ⟨le_refl _, zero_le_one⟩, by simp⟩
  have h1 : (1 : ℂ) ∈ S := ⟨1, ⟨zero_le_one, le_refl _⟩, by simp⟩
  have ht : Filter.Tendsto φ (nhds 0) (nhds z) := by
    have := hφc.tendsto 0
    simpa [φ] using this
  have hev : Filter.EventuallyEq (nhds (0 : ℂ)) (g ∘ φ) 0 :=
    (ht.eventually hz0).mono (fun t h => by simpa using h)
  have := (han.mono hSU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hSc h0 hev h1
  simpa [φ] using this

end Bl.FirstBlockLemmaJ
