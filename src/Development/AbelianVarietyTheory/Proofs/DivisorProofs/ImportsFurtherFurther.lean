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

namespace GlobalTheory.SpectralLemmaFirst

theorem main : (let d1 : {V ι : Type} → [inst : AddCommGroup V] → [inst_1 : Module ℂ V] → (ι → V →ₗ[ℂ] V) → Subalgebra ℂ (Module.End ℂ V) := @(fun {V ι : Type} [AddCommGroup V] [Module ℂ V] (ρ : ι → V →ₗ[ℂ] V) ↦ Algebra.adjoin ℂ (Set.range ρ)); ∀ {V ι : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V] {ρ : ι → V →ₗ[ℂ] V} {N : Submodule ℂ V}, (∀ (y : ι), ∀ x ∈ N, (ρ y : V → V) x ∈ N) → ∀ {s : Module.End ℂ V}, s ∈ d1 ρ → ∀ x ∈ N, (s : V → V) x ∈ N) := by
  intro d1 V ι _ _ ρ N hN s hs
  simp only [d1] at hs
  induction hs using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨y, rfl⟩ := hf
    exact hN y
  | algebraMap r =>
    intro x hx
    simpa [Module.algebraMap_end_apply] using N.smul_mem r hx
  | add f g _ _ hf hg =>
    intro x hx
    simpa using N.add_mem (hf x hx) (hg x hx)
  | mul f g _ _ hf hg =>
    intro x hx
    simpa using hf _ (hg x hx)

end GlobalTheory.SpectralLemmaFirst
