import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace PI.EllRegPr

variable {d : ℕ}

def pdc : List (Fin d) → ((Fin d → ℝ) → ℂ) → (Fin d → ℝ) → ℂ
  | [], u => u
  | i :: w, u => fun x => fderiv ℝ (pdc w u) x (Pi.single i 1)

structure DOp (d : ℕ) where
  ord : ℕ
  a : (k : Fin (ord + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → ℂ

def DOp.tr (A : DOp d) (ψ : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑ k : Fin (A.ord + 1), ∑ w : Fin k → Fin d,
    (-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => A.a k w y * ψ y) x

def DOp.symb (A : DOp d) (x ξ : Fin d → ℝ) : ℂ :=
  ∑ w : Fin A.ord → Fin d, (∏ i, (ξ (w i) : ℂ)) * A.a (Fin.last A.ord) w x

def DOp.SmoothOn (A : DOp d) (X : Set (Fin d → ℝ)) : Prop := ∀ k w, ContDiffOn ℝ ∞ (A.a k w) X

def DOp.EllipticOn (A : DOp d) (X : Set (Fin d → ℝ)) : Prop :=
  ∀ x ∈ X, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → A.symb x ξ ≠ 0

def DOp.charSet (A : DOp d) (X : Set (Fin d → ℝ)) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {p | p.1 ∈ X ∧ p.2 ≠ 0 ∧ A.symb p.1 p.2 = 0}

def IsTest (X : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ X

def distOf (u : (Fin d → ℝ) → ℂ) : ((Fin d → ℝ) → ℂ) → ℂ := fun ψ => ∫ x, u x * ψ x

def distApp (A : DOp d) (u : (Fin d → ℝ) → ℂ) : ((Fin d → ℝ) → ℂ) → ℂ := fun ψ => ∫ x, u x * A.tr ψ x

def ftD (T : ((Fin d → ℝ) → ℂ) → ℂ) (φ : (Fin d → ℝ) → ℂ) (ξ : Fin d → ℝ) : ℂ :=
  T (fun x => φ x * Complex.exp (-(Complex.I * ((x ⬝ᵥ ξ : ℝ) : ℂ))))

def wt (s : ℝ) (ξ : Fin d → ℝ) : ℝ := (1 + ξ ⬝ᵥ ξ) ^ s

def WFs (s : ℝ) (T : ((Fin d → ℝ) → ℂ) → ℂ) (X : Set (Fin d → ℝ)) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {p | p.1 ∈ X ∧ p.2 ≠ 0 ∧ ¬ ∃ (φ : (Fin d → ℝ) → ℂ) (Γ : Set (Fin d → ℝ)), IsTest X φ ∧ φ p.1 ≠ 0 ∧
    IsOpen Γ ∧ p.2 ∈ Γ ∧ (∀ η ∈ Γ, η ≠ 0) ∧ (∀ η ∈ Γ, ∀ t : ℝ, 0 < t → t • η ∈ Γ) ∧
    (∫⁻ ξ in Γ, ENNReal.ofReal (wt s ξ * Complex.normSq (ftD T φ ξ))) < ⊤}

def HsLoc (s : ℝ) (T : ((Fin d → ℝ) → ℂ) → ℂ) (X : Set (Fin d → ℝ)) : Prop :=
  ∀ φ, IsTest X φ → (∫⁻ ξ, ENNReal.ofReal (wt s ξ * Complex.normSq (ftD T φ ξ))) < ⊤

def WFsEmptyIff : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (s : ℝ), IsOpen X → ContinuousOn u X →
    (WFs s (distOf u) X = ∅ ↔ HsLoc s (distOf u) X)

def WFsChar : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (A : DOp d) (s : ℝ), IsOpen X → ContinuousOn u X →
    A.SmoothOn X → HsLoc s (distApp A u) X → WFs (s + A.ord) (distOf u) X ⊆ A.charSet X

def WFsElliptic : Prop :=
  ∀ (d : ℕ) (X : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ) (A : DOp d) (s : ℝ), IsOpen X → ContinuousOn u X →
    A.SmoothOn X → A.EllipticOn X → WFs (s - A.ord) (distApp A u) X = WFs s (distOf u) X

end PI.EllRegPr

namespace PI

def EllipticRegularity2 : Prop := EllRegPr.WFsEmptyIff ∧ EllRegPr.WFsChar ∧ EllRegPr.WFsElliptic

end PI
