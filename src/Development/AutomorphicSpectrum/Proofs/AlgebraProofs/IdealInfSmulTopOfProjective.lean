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

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem mem_ideal_smul_top_iff_coord {O : Type} [CommRing O] {L : Type} [AddCommGroup L]
    [Module O L] (s : L →ₗ[O] (L →₀ O))
    (hs : Function.LeftInverse (Finsupp.linearCombination O (id : L → L)) s)
    (𝔠 : Ideal O) (x : L) :
    x ∈ 𝔠 • (⊤ : Submodule O L) ↔ ∀ i, s x i ∈ 𝔠 := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact 𝔠.mul_mem_right _ hr
    · intro a b ha hb i
      rw [map_add, Finsupp.add_apply]
      exact 𝔠.add_mem (ha i) (hb i)
  · intro h
    rw [← hs x, Finsupp.linearCombination_apply, Finsupp.sum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem ideal_inf_smul_top_of_projective : ∀ (O : Type) [CommRing O] (L : Type) [AddCommGroup L] [Module O L] [Module.Projective O L] (𝔞 𝔟 : Ideal O), (𝔞 ⊓ 𝔟) • (⊤ : Submodule O L) = 𝔞 • (⊤ : Submodule O L) ⊓ 𝔟 • (⊤ : Submodule O L) := by
  intro O _ L _ _ hP 𝔞 𝔟
  obtain ⟨s, hs⟩ := Module.projective_def.1 hP
  ext x
  rw [Submodule.mem_inf, GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs,
    GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs,
    GlobalTheory.CompanionTheory.Ar.Cmp.mem_ideal_smul_top_iff_coord s hs]
  simp only [Submodule.mem_inf, forall_and]

end GlobalTheory.CompanionTheory.Ar.Cmp
