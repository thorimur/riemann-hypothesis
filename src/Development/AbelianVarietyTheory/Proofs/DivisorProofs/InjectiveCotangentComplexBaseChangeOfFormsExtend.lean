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
open TensorProduct KaehlerDifferential

namespace GlobalTheory

theorem injective_cotangentComplexBaseChange_of_forms_extend : ∀ (A P R K : Type) [CommRing A] [CommRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], (∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i) → Function.Injective (KaehlerDifferential.cotangentComplexBaseChange A R P K) := by
  intro A P R K _ _ _ _ _ _ _ _ _ _ _ _ _ hext
  rw [injective_iff_map_eq_zero]
  intro z hz
  refine (Module.forall_dual_apply_eq_zero_iff K z).1 fun φ => ?_
  let ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K :=
    (φ.restrictScalars P) ∘ₗ (TensorProduct.mk P K (RingHom.ker (algebraMap P R)) 1)
  obtain ⟨D, hD⟩ := hext ℓ
  let Λ : K ⊗[P] Ω[P⁄A] →ₗ[K] K := LinearMap.liftBaseChange K D.liftKaehlerDifferential
  have key : Λ ∘ₗ cotangentComplexBaseChange A R P K = φ := by
    ext i
    simp [Λ, cotangentComplexBaseChange_tmul, kerToTensor_apply, hD, ℓ]
  have h2 := congrArg (fun f => f z) key
  simpa [hz] using h2.symm

end GlobalTheory
