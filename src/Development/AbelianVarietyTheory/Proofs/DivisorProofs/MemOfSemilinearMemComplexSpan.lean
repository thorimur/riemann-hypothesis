import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

theorem mem_of_semilinear_mem_complex_span : ∀ {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V), LinearIndependent ℂ (fun k => j (b k)) → ∀ (U : Submodule K V) (x : V), j x ∈ Submodule.span ℂ (j '' (U : Set V)) → x ∈ U := by
  intro K V W ι _ _ _ _ _ _ σ j b hli U x hx
  by_contra hxU
  obtain ⟨f, hfx, hfU⟩ := U.exists_dual_map_eq_bot_of_notMem hxU inferInstance
  obtain ⟨L, hL⟩ := (Finsupp.linearCombination ℂ (fun k => j (b k))).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli)
  let g : W →ₗ[ℂ] ℂ := (Finsupp.linearCombination ℂ (fun k => σ (f (b k)))).comp L
  have hb : ∀ k, g (j (b k)) = σ (f (b k)) := by
    intro k
    have h1 : L (j (b k)) = Finsupp.single k 1 := by
      have := LinearMap.congr_fun hL (Finsupp.single k 1)
      simpa using this
    simp [g, h1]
  have hg : ∀ v, g (j v) = σ (f v) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hb k
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => rw [j.map_smulₛₗ, map_smul, map_smul, hy]; simp
  have hle : Submodule.span ℂ (j '' (U : Set V)) ≤ LinearMap.ker g := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have : f u = 0 := by
      have : f u ∈ U.map f := ⟨u, hu, rfl⟩
      rw [hfU] at this
      simpa using this
    simp [hg, this]
  have h0 : σ (f x) = 0 := by rw [← hg]; exact hle hx
  exact hfx (by simpa using h0)

end GlobalTheory
