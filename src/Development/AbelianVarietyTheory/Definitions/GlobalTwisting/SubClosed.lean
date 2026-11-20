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

noncomputable section

open scoped Matrix

namespace GlobalTheory.SeqCx

def bd (V : Type) : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun l : List V =>
    ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) (1 : ℤ)

def chains {V : Type} (F : Set (List V)) (p : ℕ) : Submodule ℤ (List V →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {l | l ∈ F ∧ l.length = p}

def ExactAt {V : Type} (F : Set (List V)) (p : ℕ) : Prop :=
  ∀ c ∈ chains F p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c

def SubClosed {V : Type} (F : Set (List V)) : Prop := ∀ l ∈ F, ∀ l' : List V, l'.Sublist l → l' ∈ F

def linkIn {V : Type} (F : Set (List V)) (S : Set V) (τ : List V) : Set (List V) :=
  {w | (∀ x ∈ w, x ∈ S) ∧ τ ++ w ∈ F}

def uniSeq (R : Type) [CommRing R] (n : ℕ) : Set (List (Fin n → R)) :=
  {l | ∃ f : Fin l.length → Fin n → R, ∀ i j : Fin l.length, f i ⬝ᵥ l.get j = if i = j then 1 else 0}

def splitSeq (R : Type) [CommRing R] (n : ℕ) : Set (List ((Fin n → R) × (Fin n → R))) :=
  {l | ∀ i j : Fin l.length, (l.get i).2 ⬝ᵥ (l.get j).1 = if i = j then 1 else 0}

example : [((fun _ => 1 : Fin 1 → ℤ), (fun _ => 1 : Fin 1 → ℤ))] ∈ splitSeq ℤ 1 := by
  intro i j
  obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
  fin_cases i
  simp [dotProduct]

end GlobalTheory.SeqCx

end
