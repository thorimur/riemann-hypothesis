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
import Mathlib.RingTheory.LaurentSeries
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

namespace Formalism.WachCohomologyFacts.TopB

def Ord {k : Type} [Field k] (j : ℤ) (x : LaurentSeries k) : Prop := ∀ i < j, x.coeff i = 0

def vv (k : Type) [Field k] : LaurentSeries k := HahnSeries.single 1 1

def IsUnitR {k : Type} [Field k] (x : LaurentSeries k) : Prop := Ord 0 x ∧ x.coeff 0 ≠ 0

structure PsiData (k : Type) [Field k] (ℓ : ℕ) where
  φ : LaurentSeries k →ₐ[k] LaurentSeries k
  γ : LaurentSeries k →ₐ[k] LaurentSeries k
  ψ : LaurentSeries k →+ LaurentSeries k
  u : LaurentSeries k
  c : LaurentSeries k
  c₀ : k
  hu : IsUnitR u
  φ_v : φ (vv k) = u * vv k ^ ℓ
  φ_ord : ∀ (j : ℤ) (x : LaurentSeries k), Ord j x → Ord (ℓ * j) (φ x)
  hc : IsUnitR c
  γ_v : γ (vv k) = vv k + c * vv k ^ 2
  γ_bij : Function.Bijective γ
  γ_φ : ∀ x, γ (φ x) = φ (γ x)
  hc₀ : c₀ ≠ 0
  γ_lead : ∀ (j : ℤ) (x : LaurentSeries k), Ord j x →
    Ord (j + 1) (γ x - x) ∧ Ord (j + 2) (γ x - x - ((j : k) * c₀) • (vv k * x))
  ψ_φ : ∀ a x, ψ (φ a * x) = a * ψ x
  ψ_one : ψ 1 = 1
  ψ_γ : ∀ x, ψ (γ x) = γ (ψ x)
  ψ_low : ∀ a : ℤ, 2 - (ℓ : ℤ) ≤ a → a ≤ 1 → ψ '' {x | Ord a x} = {x | Ord 0 x}
  ψ_high : ∀ a : ℤ, 2 ≤ a → a ≤ (ℓ : ℤ) + 1 → ψ '' {x | Ord a x} = {x | Ord 1 x}

def LemmaB : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ], ℓ.Prime → 5 ≤ ℓ →
    ∀ (P : PsiData k ℓ) (n : ℕ) (g : Fin n → Fin n → LaurentSeries k),
    (∀ i j, Ord 1 (g i j - if i = j then 1 else 0)) →
    ∀ a : ℤ, ¬ ((ℓ : ℤ) ∣ a - 1) →
    let Γ : (Fin n → LaurentSeries k) → (Fin n → LaurentSeries k) :=
      fun x m => ∑ j, P.γ (x j) * P.φ (g j m)
    let X : ℤ → Set (Fin n → LaurentSeries k) := fun b => {x | ∀ j, Ord b (x j) ∧ P.ψ (x j) = 0}
    (∀ x ∈ X a, Γ x - x ∈ X (a + 1)) ∧ (∀ x ∈ X a, Γ x = x → x = 0) ∧
      (∀ y ∈ X (a + 1), ∃ x ∈ X a, Γ x - x = y)

end Formalism.WachCohomologyFacts.TopB
