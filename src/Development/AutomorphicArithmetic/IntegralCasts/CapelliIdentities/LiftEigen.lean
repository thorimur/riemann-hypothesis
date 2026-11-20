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
import Mathlib.RepresentationTheory.Basic
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

theorem UpperTheory.Reformulated.B.R4.lift_eigen :
    ∀ {T V : Type} [inst : CommGroup T]
    [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V] (ρ : Representation ℂ T V) {ψ μ : T →* ℂˣ} {v y : V},
    (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) v = (↑((ψ : T → ℂˣ) t) : ℂ) • v) →
      μ ≠ ψ →
        y ∉ ℂ ∙ v →
          (∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) y - (↑((μ : T → ℂˣ) t) : ℂ) • y ∈ ℂ ∙ v) →
            v ≠ (0 : V) →
              ∃ (z : V), z ≠ (0 : V) ∧ ∀ (t : T), ((ρ : T → V →ₗ[ℂ] V) t : V → V) z = (↑((μ : T → ℂˣ) t) : ℂ) • z := by
  intro T V _ _ _ ρ ψ μ v y hv hne hy hmod _
  obtain ⟨s, hs⟩ : ∃ s, μ s ≠ ψ s := DFunLike.ne_iff.mp hne
  have hs' : ((μ s : ℂˣ) : ℂ) - ((ψ s : ℂˣ) : ℂ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hs (Units.ext h)
  refine ⟨ρ s y - ((ψ s : ℂˣ) : ℂ) • y, ?_, ?_⟩
  · intro h0
    apply hy
    have h1 := hmod s
    rw [sub_eq_zero.mp h0, ← sub_smul, ← neg_sub, neg_smul, neg_mem_iff] at h1
    exact (Submodule.smul_mem_iff _ hs').mp h1
  · intro t
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hmod t)
    have hty : ρ t y = ((μ t : ℂˣ) : ℂ) • y + b • v := by
      rw [hb]; abel
    have hcomm : ρ t (ρ s y) = ρ s (ρ t y) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [map_sub, map_smul, hcomm, hty, map_add, map_smul, map_smul, hv s]
    module
