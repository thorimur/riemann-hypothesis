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
import Mathlib.LinearAlgebra.Matrix.PosDef
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

open NumberField Matrix
open scoped ComplexOrder

noncomputable section

namespace PI.HermLatFin

def herm {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def IsLat {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin n → E)) = ⊤

def admitted {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  IsLat L ∧ (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm σ J x y)) ∧
    ∀ y : Fin n → E, (∀ x ∈ L, IsIntegral ℤ (herm σ J x y)) → (T : E) • y ∈ L

def IsUJ {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J g : Matrix (Fin n) (Fin n) E) : Prop :=
  (g.map σ)ᵀ * J * g = J

def HermLatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (T : ℕ),
    (∀ τ : E →+* ℂ, ∀ a : E, τ (σ a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, (J.map τ).PosDef) →
    0 < T →
    ∃ S : Set (Submodule (𝓞 E) (Fin n → E)), S.Finite ∧
      ∀ L, admitted σ J T L → ∃ L' ∈ S, ∃ g : Matrix (Fin n) (Fin n) E, IsUJ σ J g ∧
        (fun x => g *ᵥ x) '' (L' : Set (Fin n → E)) = (L : Set (Fin n → E))

end PI.HermLatFin
