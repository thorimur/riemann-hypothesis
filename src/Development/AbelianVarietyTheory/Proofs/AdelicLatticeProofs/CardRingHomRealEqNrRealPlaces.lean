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
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem card_ringHom_real_eq_nrRealPlaces :
    ∀ (F : Type) [Field F] [NumberField F], Nat.card (F →+* ℝ) = InfinitePlace.nrRealPlaces F := by
  intro F _ _
  let e : (F →+* ℝ) ≃ {φ : F →+* ℂ // ComplexEmbedding.IsReal φ} :=
    { toFun := fun ψ => ⟨Complex.ofRealHom.comp ψ, by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]⟩
      invFun := fun φ => φ.2.embedding
      left_inv := fun ψ => by
        ext x
        simp [ComplexEmbedding.IsReal.embedding]
      right_inv := fun φ => by
        apply Subtype.ext
        ext x
        simp }
  classical
  rw [Nat.card_congr (e.trans InfinitePlace.mkReal), Nat.card_eq_fintype_card]

end GlobalTheory.QNorm
