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
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
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
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FiniteComplete

theorem isAdicComplete_of_finite : ∀ (O M : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [AddCommGroup M] [Module O M]
    [Module.Finite O M], IsAdicComplete (IsLocalRing.maximalIdeal O) M := by
  intro O M _ _ _ hO _ _ _
  set I := IsLocalRing.maximalIdeal O
  have hb : Function.Bijective (AdicCompletion.of I O) := AdicCompletion.of_bijective_iff.2 hO
  let φ : O ≃ₗ[O] AdicCompletion I O := LinearEquiv.ofBijective (AdicCompletion.of I O) hb
  let e : M ≃ₗ[O] AdicCompletion I O ⊗[O] M :=
    (TensorProduct.lid O M).symm.trans (TensorProduct.congr φ (LinearEquiv.refl O M))
  have h1 : AdicCompletion.of I O 1 = 1 := by
    ext n
    simp
  have hfac : ⇑(AdicCompletion.of I M) = ⇑(AdicCompletion.ofTensorProduct I M) ∘ ⇑e := by
    funext m
    have he : e m = (1 : AdicCompletion I O) ⊗ₜ[O] m := by
      simp [e, φ, h1]
    simp [he]
  refine AdicCompletion.of_bijective_iff.1 ?_
  rw [hfac]
  exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).comp e.bijective

end GlobalTheory.CompanionTheory.FiniteComplete
