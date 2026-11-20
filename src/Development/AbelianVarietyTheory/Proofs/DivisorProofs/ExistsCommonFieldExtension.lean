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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

open scoped TensorProduct

namespace GlobalTheory

theorem exists_common_field_extension :
    ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] (i₁ : Ω →+* Ω₁) (i₂ : Ω →+* Ω₂),
      ∃ (Ω₃ : Type) (_ : Field Ω₃) (j₁ : Ω₁ →+* Ω₃) (j₂ : Ω₂ →+* Ω₃), j₁.comp i₁ = j₂.comp i₂ := by
  intro Ω Ω₁ Ω₂ _ _ _ i₁ i₂
  letI : Algebra Ω Ω₁ := i₁.toAlgebra
  letI : Algebra Ω Ω₂ := i₂.toAlgebra
  haveI : Nontrivial (Ω₁ ⊗[Ω] Ω₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Ω₁ ⊗[Ω] Ω₂)
  refine ⟨(Ω₁ ⊗[Ω] Ω₂) ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := Ω) (A := Ω₁) (B := Ω₂)).toRingHom, ?_⟩
  ext x
  have h : (algebraMap Ω Ω₁ x) ⊗ₜ[Ω] (1 : Ω₂) = (1 : Ω₁) ⊗ₜ[Ω] (algebraMap Ω Ω₂ x) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact congrArg (Ideal.Quotient.mk m) h

end GlobalTheory
