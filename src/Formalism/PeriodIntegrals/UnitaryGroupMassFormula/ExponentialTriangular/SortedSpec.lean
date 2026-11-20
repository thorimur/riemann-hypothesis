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

open Matrix Finset

noncomputable section

namespace PI.ET

def SortedSpec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ) : Prop :=
  Antitone d ∧ ∃ W ∈ Matrix.unitaryGroup (Fin n) ℂ,
    A = W * Matrix.diagonal (fun i => (d i : ℂ)) * Wᴴ

def psum {n : ℕ} (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), f i

def SpecExists : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Aᴴ = A → ∃ d : Fin n → ℝ, SortedSpec A d

def HSEq : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), SortedSpec A d →
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = ∑ i, d i ^ 2

def KyFanDet : Prop :=
  ∀ (n k : ℕ) (hk : k ≤ n) (p : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ)
    (V : Matrix (Fin n) (Fin k) ℂ),
    Antitone p → (∀ i, 0 < p i) → W ∈ Matrix.unitaryGroup (Fin n) ℂ → Vᴴ * V = 1 →
    ‖(Vᴴ * (W * Matrix.diagonal (fun i => (p i : ℂ)) * Wᴴ) * V).det‖ ≤
      ∏ i : Fin k, p (Fin.castLE hk i)

def Horn : Prop :=
  ∀ (n : ℕ) (X Y Z U : Matrix (Fin n) (Fin n) ℂ) (ξ η ζ : Fin n → ℝ),
    SortedSpec X ξ → SortedSpec Y η → SortedSpec Z ζ → U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    NormedSpace.exp X * NormedSpace.exp Y = U * NormedSpace.exp Z →
    (∀ k ≤ n, psum ζ k ≤ psum (fun i => ξ i + η i) k) ∧ ∑ i, ζ i = ∑ i, (ξ i + η i)

def AbelSq : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℝ), Antitone a → (∀ k ≤ n, psum a k ≤ psum b k) →
    ∑ i, a i = ∑ i, b i → ∑ i, a i ^ 2 ≤ ∑ i, b i ^ 2

def EuclTri : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℝ),
    Real.sqrt (∑ i, (a i + b i) ^ 2) ≤ Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2)

end PI.ET
