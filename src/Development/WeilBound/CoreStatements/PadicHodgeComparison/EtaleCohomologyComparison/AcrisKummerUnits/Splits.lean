import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.DividedPowers.Basic
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

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.R

variable {S : Type} [CommRing S]

variable (S) in

def Aic : Prop := ∀ P : Polynomial S, P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x

def Val (ϖ : S) : Prop := ∀ f g : S, (∃ N : ℕ, ϖ ^ N ∈ Ideal.span {f, g}) →
  ∃ e : S, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}

variable (S) in

def Val0 : Prop := ∀ f g : S, ∃ e : S, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}

def Val2 (ϖ : S) : Prop := ∀ f g : S, ∃ e : S, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g, ϖ ^ 2} ∧
  (1 - e) * g ∈ Ideal.span {f, ϖ ^ 2}

def Dich (ϖ : S) : Prop := ∀ f g : S, (∃ N : ℕ, ϖ ^ N ∈ Ideal.span {f, g}) → g ∣ f ∨ f ∣ g

variable (S) in

def Loc : Prop := ∀ f : S, ∃ e : S, IsIdempotentElem e ∧ e ∈ Ideal.span {f} ∧ 1 - e ∈ Ideal.span {1 - f}

def compI (P : Ideal S) : Ideal S := Ideal.span {e | IsIdempotentElem e ∧ e ∈ P}

def Step (ϖ : S) : Prop := ∀ (Q : Polynomial S) (n : ℕ), Q.Monic → 0 < Q.natDegree → ϖ ^ n ∣ Q.eval 0 →
  ∃ z, ϖ ^ (n + 1) ∣ Q.eval z ∧ ϖ ^ n ∣ z ^ Q.natDegree

def Roots (ϖ : S) : Prop := ∀ (f : S) (N i : ℕ), f ∣ ϖ ^ N → 0 < i → ∃ (r : S) (u : Sˣ), f = u * r ^ i

def Splits (U : Scheme.{0}) : Prop := ∀ (Y : Scheme.{0}) (f : Y ⟶ U), Etale f → Surjective f → ∃ s : U ⟶ Y, s ≫ f = 𝟙 U

def SecOn {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of S)) (e : S) : Prop :=
  ∃ s : Spec (CommRingCat.of (Localization.Away e)) ⟶ Y, s ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away e)))

variable (S) in

def TF : Prop := ∀ k : ℕ, k ≠ 0 → (k : S) ∈ nonZeroDivisors S

def PdI (I : Ideal S) : Prop := ∀ x ∈ I, ∀ k : ℕ, k ≠ 0 → ∃ y ∈ I, (k.factorial : S) * y = x ^ k

def IsPd {E : Type} [CommRing E] (π : S →+* E) (I : Ideal S) {J : Ideal E} (δ : DividedPowers J) : Prop :=
  J = I.map π ∧ ∀ (k : ℕ) (x y : S), x ∈ I → (k.factorial : S) * y = x ^ k → δ.dpow k (π x) = π y

end CrystallineSemistableComparison.R
