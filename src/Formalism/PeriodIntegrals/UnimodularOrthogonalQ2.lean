import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
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
import Mathlib.NumberTheory.Padics.Complex
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

namespace PI.UnimodularOrthogonalQ2

open NumberField

def OKpair (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) :
    Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K))))

def hP {p : ℕ} [Fact p.Prime] {κ : Type} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

def IsBasisOver {p : ℕ} [Fact p.Prime] (O : Set (ℂ_[p] × ℂ_[p])) {κ ι : Type} [Fintype ι]
    (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e, b e ∈ Y) ∧ ∀ y ∈ Y, ∃! a : ι → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ O) ∧ y = fun k => ∑ e, a e * b e k

def Stmt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) (d : ℕ) (b0 : K),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → d.Prime → b0 ^ 2 = -(d : K) → p ≠ d → (p = 2 → d % 8 = 7) →
    ∀ (κ : Type) [Fintype κ] (r : ℕ) (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : Fin r → κ → ℂ_[p] × ℂ_[p]),
      IsBasisOver (OKpair K c p τ) Y b →
      (∀ a : Fin r → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ OKpair K c p τ) → (fun k => ∑ e, a e * b e k) ∈ Y) →
      (∀ i j, hP (b i) (b j) ∈ OKpair K c p τ) →
      (∃ G : Fin r → Fin r → ℂ_[p] × ℂ_[p], (∀ i j, G i j ∈ OKpair K c p τ) ∧
        ∀ i k, ∑ j, hP (b i) (b j) * G j k = if i = k then 1 else 0) →
      ∃ b' : Fin r → κ → ℂ_[p] × ℂ_[p], IsBasisOver (OKpair K c p τ) Y b' ∧
        ∀ i j, hP (b' i) (b' j) = if i = j then 1 else 0

end PI.UnimodularOrthogonalQ2
