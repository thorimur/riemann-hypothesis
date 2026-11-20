import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
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

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

def cons (γ : Γ) (σ : ℕ → Γ) : ℕ → Γ := fun n => match n with
  | 0 => γ
  | n + 1 => σ n

def skip (i : ℕ) (σ : ℕ → Γ) : ℕ → Γ := fun n => if n < i then σ n else σ (n + 1)

def psi (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) (γ : Γ) (h : V) : ℝ := φ (A γ⁻¹ h)

def Kf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {q : ℕ} (β : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ)
    (σ : ℕ → Γ) (h : V) : V [⋀^Fin q]→L[ℝ] ℝ :=
  ∑ᶠ γ, psi A φ γ h • β (cons γ σ) h

def eta (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) :
    (j : ℕ) → (ℕ → Γ) → V → V [⋀^Fin j]→L[ℝ] ℝ
  | 0, σ => fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => σ i)
  | j + 1, σ => extDeriv (Kf A φ (eta A φ c j) σ)

def delG (n : ℕ) {X : Type} [AddCommGroup X] [Module ℝ X] (β : (ℕ → Γ) → X) (σ : ℕ → Γ) : X :=
  ∑ i ∈ Finset.range (n + 2), (-1 : ℝ) ^ i • β (skip i σ)

def dC' {Y : Type} {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : (Fin (m + 2) → Y) → ℝ :=
  fun y => ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F fun j => y (i.succAbove j)

def intS' {q : ℕ} (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (y : Fin (q + 1) → V) : ℝ :=
  ∫ t in {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1},
    ω (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0

structure Hyp (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) : Prop where
  isOpen : IsOpen U
  convex : Convex ℝ U
  mapsTo : ∀ g, ∀ h ∈ U, A g h ∈ U
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) φ U
  locFin : LocallyFinite fun γ : Γ => {h : U | φ (A γ⁻¹ h) ≠ 0}
  sum_one : ∀ h ∈ U, ∑ᶠ γ, φ (A γ⁻¹ h) = 1

structure Coc {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) : Prop where
  inv : ∀ g y, c (fun j => g * y j) = c y
  coc : ∀ y : Fin (k + 3) → Γ, ∑ i : Fin (k + 3), (-1 : ℝ) ^ (i : ℕ) * c (fun j => y (i.succAbove j)) = 0

end PositivityTheory.KB.WhittakerCocycle

end
