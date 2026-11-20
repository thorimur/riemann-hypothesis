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
import Mathlib.RingTheory.RingHom.Unramified
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
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

theorem compositum_finite_formallyUnramified : ∀ {k K L : Type} [Field k] [Field K] [Field L] (i : k →+* K) (j : k →+* L), i.Finite → i.FormallyUnramified → ∃ (M : Type) (_ : Field M) (u : K →+* M) (v : L →+* M), u.comp i = v.comp j ∧ v.Finite ∧ v.FormallyUnramified := by
  intro k K L _ _ _ i j hf hu
  letI : Algebra k K := i.toAlgebra
  letI : Algebra k L := j.toAlgebra
  haveI : Module.Finite k K := hf
  haveI : Algebra.FormallyUnramified k K := hu
  haveI : Nontrivial (L ⊗[k] K) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[k] K)
  letI : Field (L ⊗[k] K ⧸ m) := Ideal.Quotient.field m
  refine ⟨L ⊗[k] K ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight : K →ₐ[k] L ⊗[k] K).toRingHom,
    algebraMap L (L ⊗[k] K ⧸ m), ?_, ?_, ?_⟩
  · ext a
    show Ideal.Quotient.mk m (1 ⊗ₜ (algebraMap k K a)) = Ideal.Quotient.mk m (algebraMap L (L ⊗[k] K) (algebraMap k L a))
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact (RingHom.formallyUnramified_algebraMap).mpr inferInstance

end GlobalTheory
