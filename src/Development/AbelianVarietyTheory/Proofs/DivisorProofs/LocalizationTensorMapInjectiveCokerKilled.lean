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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem localization_map_injective_coker_killed (R A B : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B) :
    Function.Injective ψ → ∀ s : R, s ≠ 0 → (∀ b : B, s • b ∈ ψ.range) →
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) ∧
      algebraMap R (Localization.AtPrime p) s ≠ 0 ∧
      ∀ y : Localization.AtPrime p ⊗[R] B, algebraMap R (Localization.AtPrime p) s • y ∈
        (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ).range := by
  intro hψ s hs hrange
  set L := Localization.AtPrime p
  refine ⟨?_, ?_, ?_⟩
  · have heq : ((Algebra.TensorProduct.map (AlgHom.id L L) ψ).toLinearMap.restrictScalars R) =
        LinearMap.lTensor L ψ.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      simp
    have : Function.Injective (LinearMap.lTensor L ψ.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hψ
    rw [← heq] at this
    exact this
  · intro h0
    apply hs
    have hinj : Function.Injective (algebraMap R L) :=
      IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors p)
    exact hinj (by rw [h0, map_zero])
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      obtain ⟨a, ha⟩ := hrange b
      refine ⟨t ⊗ₜ a, ?_⟩
      have ha' : ψ a = s • b := ha
      change Algebra.TensorProduct.map (AlgHom.id L L) ψ (t ⊗ₜ a) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ha', TensorProduct.smul_tmul', algebraMap_smul,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      rw [smul_add]
      exact Subalgebra.add_mem _ hx hy

end GlobalTheory
