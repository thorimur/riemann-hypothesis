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

namespace Reformulated.AlgebraicInfinityType

open NumberField

@[ext]
structure InfinityType (F : Type*) [Field F] (n : ℕ) where

  pairs : (F →+* ℂ) → Multiset (ℂ × ℂ)
  card_pairs : ∀ σ, Multiset.card (pairs σ) = n
  sub_int : ∀ σ, ∀ p ∈ pairs σ, ∃ m : ℤ, p.1 - p.2 = m
  pairs_conjugate : ∀ σ, pairs (ComplexEmbedding.conjugate σ) = (pairs σ).map Prod.swap

namespace InfinityType

variable {F : Type*} [Field F] {n : ℕ}

def exponents (t : InfinityType F n) (σ : F →+* ℂ) : Multiset ℂ :=
  (t.pairs σ).map Prod.fst

def IsLAlgebraic (t : InfinityType F n) : Prop :=
  ∀ σ, ∀ a ∈ t.exponents σ, ∃ m : ℤ, a = m

def IsAlgebraic (t : InfinityType F n) : Prop :=
  ∀ σ, ∀ a ∈ t.exponents σ, ∃ m : ℤ, a = ((n : ℂ) - 1) / 2 + m

def IsRegular (t : InfinityType F n) : Prop :=
  ∀ σ, (t.exponents σ).Nodup

def IsRegularAlgebraic (t : InfinityType F n) : Prop :=
  t.IsAlgebraic ∧ t.IsRegular

def twist (t : InfinityType F n) (s : ℂ) : InfinityType F n where
  pairs σ := (t.pairs σ).map fun p => (p.1 + s, p.2 + s)
  card_pairs σ := by simp [t.card_pairs]
  sub_int σ p hp := by
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
    simpa using t.sub_int σ q hq
  pairs_conjugate σ := by simp [t.pairs_conjugate]

theorem exponents_conjugate (t : InfinityType F n) (σ : F →+* ℂ) :
    t.exponents (ComplexEmbedding.conjugate σ) = (t.pairs σ).map Prod.snd := by
  simp [exponents, t.pairs_conjugate]

theorem isAlgebraic_iff_twist (t : InfinityType F n) :
    t.IsAlgebraic ↔ (t.twist ((1 - (n : ℂ)) / 2)).IsLAlgebraic := by
  simp only [IsAlgebraic, IsLAlgebraic, exponents, twist, Multiset.map_map,
    Multiset.forall_mem_map_iff, Function.comp]
  refine forall_congr' fun σ => forall₂_congr fun p _ => exists_congr fun m => ?_
  constructor <;> intro h <;> linear_combination h

end InfinityType

def RegularAlgebraicInfinityType (F : Type*) [Field F] (n : ℕ) : Type _ :=
  {t : InfinityType F n // t.IsRegularAlgebraic}

end Reformulated.AlgebraicInfinityType
