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
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.PadicNumbers
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

noncomputable section

namespace PI.CntNotIntW

open scoped TensorProduct

def piMap (K : Type) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [Algebra ℚ_[ℓ] Fp] (ι : K →+* Fp) :
    ℚ_[ℓ] ⊗[ℚ] K →ₐ[ℚ_[ℓ]] Fp :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[ℓ] Fp) ι.toRatAlgHom (fun _ _ => Commute.all _ _)

def PiSurj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [ValuativeRel Fp]
    [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp],
    Continuous (algebraMap ℚ_[ℓ] Fp) → FiniteDimensional ℚ_[ℓ] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
      Function.Surjective (piMap K ℓ Fp ι)

theorem piMap_one_tmul (K : Type) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [Algebra ℚ_[ℓ] Fp]
    (ι : K →+* Fp) (y : K) : piMap K ℓ Fp ι (1 ⊗ₜ y) = ι y := by
  simp [piMap]

end PI.CntNotIntW
