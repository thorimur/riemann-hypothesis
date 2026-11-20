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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem ker_retraction_fg : ∀ (D T E : Type) [CommRing D] [CommRing T] [Algebra D T] [CommRing E] [Algebra D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → ∀ χ : E →ₐ[D] T, χ.comp ι = AlgHom.id D T → (RingHom.ker χ).FG := by
  intro D T E _ _ _ _ _ ι F hF χ hχ
  have hχι : ∀ t, χ (ι t) = t := fun t => by simpa using DFunLike.congr_fun hχ t
  set J : Ideal E := Ideal.span ((fun f => f - ι (χ f)) '' (F : Set E)) with hJ
  have key : ∀ x, x - ι (χ x) ∈ J := by
    intro x
    have hx : x ∈ Algebra.adjoin D (Set.range ι ∪ (F : Set E)) := by rw [hF]; exact Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨t, rfl⟩ | hx
      · simp [hχι]
      · exact Ideal.subset_span ⟨x, hx, rfl⟩
    | algebraMap r => simp [AlgHom.commutes]
    | add x y _ _ hx hy =>
      have e : x + y - ι (χ (x + y)) = (x - ι (χ x)) + (y - ι (χ y)) := by
        simp only [map_add]; ring
      rw [e]; exact J.add_mem hx hy
    | mul x y _ _ hx hy =>
      have e : x * y - ι (χ (x * y)) = (x - ι (χ x)) * y + ι (χ x) * (y - ι (χ y)) := by
        simp only [map_mul]; ring
      rw [e]; exact J.add_mem (J.mul_mem_right _ hx) (J.mul_mem_left _ hy)
  have hker : RingHom.ker χ = J := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      simpa [hx] using key x
    · rw [hJ, Ideal.span_le]
      rintro _ ⟨f, _, rfl⟩
      simp [RingHom.mem_ker, hχι]
  rw [hker]
  classical
  exact ⟨F.image (fun f => f - ι (χ f)), by rw [Finset.coe_image]⟩

end GlobalTheory
