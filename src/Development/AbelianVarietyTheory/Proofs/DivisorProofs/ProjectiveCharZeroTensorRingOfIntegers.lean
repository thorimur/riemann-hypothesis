import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RingTheory.SimpleRing.Principal
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
open scoped TensorProduct

namespace GlobalTheory

theorem isReduced_charZero_tensor_ringOfIntegers (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] : IsReduced (k ⊗[ℤ] 𝓞 F) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  haveI : IsReduced (k ⊗[ℤ] F) := Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[ℤ] F)
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℤ k) (IsScalarTower.toAlgHom ℤ (𝓞 F) F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective _ hinj

instance isSemisimpleRing_charZero_tensor_ringOfIntegers (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] : IsSemisimpleRing (k ⊗[ℤ] 𝓞 F) := by
  haveI := isReduced_charZero_tensor_ringOfIntegers F k
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 F) := IsArtinianRing.of_finite k _
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem projective_charZero_tensor_ringOfIntegers : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] 𝓞 F) M], Module.Projective (k ⊗[ℤ] 𝓞 F) M := by
  intro F _ _ k _ _ M _ _
  exact Module.projective_of_isSemisimpleRing _ _

end GlobalTheory
