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

namespace GlobalTheory.CommonAlgClosedExtension

open scoped TensorProduct

theorem exists_common_algClosed_extension (K₀ K K' : Type) [Field K₀] [Field K] [Field K']
    (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      RingHom.comp j i = RingHom.comp j' i' := by
  letI : Algebra K₀ K := i.toAlgebra
  letI : Algebra K₀ K' := i'.toAlgebra
  haveI : Nontrivial (K ⊗[K₀] K') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  letI : Field ((K ⊗[K₀] K') ⧸ m) := Ideal.Quotient.field m
  let φ : (K ⊗[K₀] K') →+* AlgebraicClosure ((K ⊗[K₀] K') ⧸ m) :=
    (algebraMap ((K ⊗[K₀] K') ⧸ m) _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[K₀] K') ⧸ m), inferInstance, inferInstance,
    φ.comp (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).toRingHom,
    φ.comp (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).toRingHom, ?_⟩
  ext x
  have h1 := (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).commutes x
  have h2 := (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).commutes x
  exact congrArg φ (h1.trans h2.symm)

end GlobalTheory.CommonAlgClosedExtension
