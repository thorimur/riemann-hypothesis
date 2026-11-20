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

namespace Formalism.RankGapBounds.LocalQuadraticParts

open Finset

abbrev Hgrp (e : ℕ) := (ZMod (4 * 2 ^ e))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod (4 * 2 ^ e))ˣ)

def hOf (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Hgrp e :=
  QuotientGroup.mk (ZMod.unitOfCoprime l hl)

def OrdersIff : Prop :=
  ∀ (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)), j ≤ e →
    ((hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1))

def OrdersBound : Prop :=
  ∀ (e J l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)), 1 ≤ J → 1 < l →
    orderOf (hOf e l hl) ≤ J → (4 * 2 ^ e : ℝ) / J - 1 ≤ l

def OrdersSumSq : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J →
    (∀ l ∈ s, l.Prime ∧ l ≠ 2 ∧ ∃ hl : Nat.Coprime l (4 * 2 ^ e), orderOf (hOf e l hl) ≤ J) →
    ∑ l ∈ s, Real.log l / (l : ℝ) ^ 2 ≤ C * J ^ 2 * Real.log (2 ^ e) / ((2 : ℝ) ^ e) ^ 2

def OrdersSumY : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (Y : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
    (∀ l ∈ s, l.Prime ∧ l ≠ 2 ∧ (l : ℝ) ≤ Y ∧
      ∃ hl : Nat.Coprime l (4 * 2 ^ e), orderOf (hOf e l hl) ≤ J) →
    ∑ l ∈ s, Real.log l / (l : ℝ) ≤ C * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e

noncomputable def wt {α : Type*} [Fintype α] (δ : ℝ) (T : Finset α) : ℝ :=
  δ ^ T.card * (1 - δ) ^ (Fintype.card α - T.card)

def RandomSubsetAvoidsBadEvents : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p

def RandomSubsetCounterexample : Prop := ¬ RandomSubsetAvoidsBadEvents

def TopsFixed : Prop :=
  ∀ (α ι : Type) [Fintype α] [DecidableEq α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ)
    (BAD : ι → α → Finset α → Prop) [∀ p t T, Decidable (BAD p t T)],
    0 < δ → δ ≤ 1 → 6 ≤ δ * Fintype.card α → 0 ≤ β → (∀ p, 0 ≤ ω p) →
    (∀ p t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T), wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) ≤ 4 * β * δ * Fintype.card α * ∑ p, ω p

end Formalism.RankGapBounds.LocalQuadraticParts
