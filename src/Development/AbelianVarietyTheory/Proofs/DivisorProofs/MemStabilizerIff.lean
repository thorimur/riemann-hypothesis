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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.MassConj

@[ext]
structure ConjPair (H X : Type) where

  elt : H

  pt : X

variable {H X : Type} [Group H] [MulAction H X]

instance : MulAction H (ConjPair H X) where
  smul δ p := ⟨δ * p.elt * δ⁻¹, δ • p.pt⟩
  one_smul p := by
    show ConjPair.mk _ _ = p
    ext <;> simp
  mul_smul δ ε p := by
    show ConjPair.mk (δ * ε * p.elt * (δ * ε)⁻¹) ((δ * ε) • p.pt) =
      ConjPair.mk (δ * (ε * p.elt * ε⁻¹) * δ⁻¹) (δ • ε • p.pt)
    ext
    · simp only; group
    · exact mul_smul δ ε p.pt

@[simp] theorem smul_elt (δ : H) (p : ConjPair H X) : (δ • p).elt = δ * p.elt * δ⁻¹ := rfl

@[simp] theorem smul_pt (δ : H) (p : ConjPair H X) : (δ • p).pt = δ • p.pt := rfl

theorem stabilizer_le_pt (p : ConjPair H X) :
    MulAction.stabilizer H p ≤ MulAction.stabilizer H p.pt := by
  intro δ hδ
  rw [MulAction.mem_stabilizer_iff] at hδ ⊢
  rw [← smul_pt, hδ]

theorem mem_stabilizer_iff (δ : H) (p : ConjPair H X) :
    δ ∈ MulAction.stabilizer H p ↔ δ * p.elt = p.elt * δ ∧ δ • p.pt = p.pt := by
  rw [MulAction.mem_stabilizer_iff, ConjPair.ext_iff, smul_elt, smul_pt]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    calc δ * p.elt = δ * p.elt * δ⁻¹ * δ := by group
      _ = p.elt * δ := by rw [h1]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1]; group

end GlobalTheory.MassConj
