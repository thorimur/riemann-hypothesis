import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.Young.YoungDiagram
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

namespace PI.IsoDualPair

def ColChoice {Lt : Type} (N1 : ℕ) (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def colsOf {k : Type} [Zero k] {N : ℕ} (Y : Matrix (Fin N) (Fin N) k) : Fin N → ℕ → k :=
  fun a j => if h : j < N then Y a ⟨j, h⟩ else 0

abbrev LaC {Lt : Type} (N : ℕ) (nu : Lt → YoungDiagram) : Type := ColChoice N nu → ℂ

def hvC {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) (x : Lt → Fin N → ℕ → ℂ) : LaC N nu :=
  fun J => minY N nu J x

def Vnu {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : Submodule ℂ (LaC N nu) :=
  Submodule.span ℂ (Set.range (hvC N nu))

def l2 {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ : LaC N nu) : ℝ := ∑ᶠ J, ‖φ J‖ ^ 2

def prC {Lt : Type} {N : ℕ} {nu : Lt → YoungDiagram} (φ ψ : LaC N nu) : ℂ := ∑ᶠ J, φ J * ψ J

def VnuMap {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram) (f : Lt → Matrix (Fin N') (Fin N) ℂ)
    (φ : LaC N nu) : LaC N' nu :=
  fun I => ∑ᶠ J : ColChoice N nu, (∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))) * φ J

def IsoDualPair : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram),
    (∀ φ ∈ Vnu N nu, (∀ ψ ∈ Vnu N nu, ‖prC φ ψ‖ ^ 2 ≤ l2 φ * l2 ψ) ∧
      ∃ ψ ∈ Vnu N nu, l2 ψ = l2 φ ∧ prC φ ψ = (l2 φ : ℂ)) ∧
    ∀ Λ : Vnu N nu →ₗ[ℂ] ℂ, ∃ φ ∈ Vnu N nu, ∀ ψ : Vnu N nu, Λ ψ = prC φ (ψ : LaC N nu)

end PI.IsoDualPair
