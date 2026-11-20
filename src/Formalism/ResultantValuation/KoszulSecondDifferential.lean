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

open Polynomial

noncomputable section

namespace Formalism.ResultantValuation

def AdjugateRankOne : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin n) R), A.det = 0 →
    ∀ k l : Fin n, A.adjugate k l • A.adjugate =
      Matrix.vecMulVec (fun i => A.adjugate i l) (fun j => A.adjugate k j)

def koszulFirstDifferential {A : Type} [CommRing A] (r : ℕ) (x y : A) :
    (Fin r → A) →ₗ[A] (Fin r → A) × (Fin r → A) :=
  LinearMap.prod (x • LinearMap.id) (y • LinearMap.id)

def koszulSecondDifferential {A : Type} [CommRing A] (r : ℕ) (x y : A) :
    (Fin r → A) × (Fin r → A) →ₗ[A] (Fin r → A) :=
  y • LinearMap.fst A (Fin r → A) (Fin r → A) - x • LinearMap.snd A (Fin r → A) (Fin r → A)

abbrev koszulFirstCohomology {A : Type} [CommRing A] (r : ℕ) (x y : A) : Type :=
  LinearMap.ker (koszulSecondDifferential r x y) ⧸
    (LinearMap.range (koszulFirstDifferential r x y)).comap (LinearMap.ker (koszulSecondDifferential r x y)).subtype

abbrev truncPoly (k : Type) [Field k] (n : ℕ) : Type := k[X] ⧸ Ideal.span {(X : k[X]) ^ n}

def KoszulLength : Prop :=
  ∀ (k : Type) [Field k] (n r : ℕ), 1 ≤ n → ∀ (u : (truncPoly k n)ˣ) (w : truncPoly k n),
    Module.length (truncPoly k n)
      (koszulFirstCohomology r (Ideal.Quotient.mk _ X * (u : truncPoly k n))
        (Ideal.Quotient.mk _ X * w)) = ((2 * r : ℕ) : ℕ∞)

open Classical in

def ComplementCount : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (r t : ℕ), Module.finrank F V = r + t → ∀ v : Fin r → V,
    Nat.card {U : Submodule F V //
        Module.finrank F U = t ∧ Submodule.span F (Set.range v) ⊔ U = ⊤} =
      if LinearIndependent F v then Fintype.card F ^ (r * t) else 0

def SubspaceMobius : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V],
    (∑ᶠ W : Submodule F V, (-1 : ℤ) ^ Module.finrank F W *
        (Fintype.card F : ℤ) ^ (Module.finrank F W).choose 2) =
      if Module.finrank F V = 0 then 1 else 0

def parabolicSet (F : Type) [Field F] (r t : ℕ) : Set (GL (Fin (r + t)) F) :=
  {g | ∀ i j : Fin (r + t), r ≤ (i : ℕ) → (j : ℕ) < r → (g : Matrix (Fin (r + t)) (Fin (r + t)) F) i j = 0}

def ParabolicConstant : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (r t : ℕ),
    (∏ i ∈ Finset.Icc 1 r, (1 - (Fintype.card F : ℝ) ^ (-(i : ℤ)))) *
        ((Nat.card (GL (Fin (r + t)) F) : ℝ) / (Nat.card (parabolicSet F r t) : ℝ)) *
        (∏ i ∈ Finset.Icc (t + 1) (r + t), (1 - (Fintype.card F : ℝ) ^ (-(i : ℤ))))⁻¹ =
      (Fintype.card F : ℝ) ^ (r * t)

def CMFactorUnit : Prop :=
  ∀ (K : Type) [Field K] (q ε X : K) (m : ℕ), q = 1 → ε ^ 2 = 1 → Odd m → X ^ m = 1 → X ≠ 1 →
    (1 - X * ε) * (1 - X⁻¹ * ε) + (q - 1) * ε ^ 2 ≠ 0

end Formalism.ResultantValuation
