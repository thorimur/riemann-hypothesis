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
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_section_of_fractionalIdeal_values {F V : Type} [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L)
    (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) {v : V} (K : FractionalIdeal (𝓞 F)⁰ F)
    (hK : K ≠ 0) (hKL : ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) :
    ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L := by
  have hmul : K * K⁻¹ = 1 := mul_inv_cancel₀ hK
  have key : ∀ s ∈ K * K⁻¹, ∃ w : V, B w v = s ∧ ∀ t ∈ K, t • w ∈ L := by
    intro s hs
    refine FractionalIdeal.mul_induction_on hs ?_ ?_
    · intro k hk k' hk'
      obtain ⟨z, hz, rfl⟩ := (hKL k).1 hk
      refine ⟨k' • z, by simp [mul_comm], fun t ht => ?_⟩
      have h1 : t * k' ∈ K * K⁻¹ := FractionalIdeal.mul_mem_mul ht hk'
      rw [hmul, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨r, hr⟩ := h1
      rw [smul_smul, ← hr]
      exact hLsmul r z hz
    · rintro x y ⟨w, hw, hw'⟩ ⟨u, hu, hu'⟩
      refine ⟨w + u, by simp [hw, hu], fun t ht => ?_⟩
      rw [smul_add]
      exact hLadd _ (hw' t ht) _ (hu' t ht)
  refine key 1 ?_
  rw [hmul]
  exact FractionalIdeal.one_mem_one _

end GlobalTheory
