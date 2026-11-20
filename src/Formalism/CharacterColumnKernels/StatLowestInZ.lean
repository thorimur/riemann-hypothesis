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

open Finset Classical

noncomputable section

namespace Formalism.NG

def blockSum {Ir ι : Type*} (tw : ℤ → Ir → Ir) (I : Finset ι) (rp : ι → Multiset Ir) (dd : ι → ℕ) :
    Multiset Ir :=
  ∑ i ∈ I, ∑ k ∈ range (dd i), (rp i).map (tw ((dd i : ℤ) - 1 - 2 * k))

def StatLowestInZ : Prop :=
  ∀ (Ir Irb : Type*) (rk : Ir → ℕ) (wt : Ir → ℤ) (tw : ℤ → Ir → Ir) (red : Ir → Multiset Irb)
    (rkb : Irb → ℕ),
    (∀ σ, 1 ≤ rk σ) → (∀ τ, 1 ≤ rkb τ) → (∀ σ, ((red σ).map rkb).sum = rk σ) →
    (∀ σ, tw 0 σ = σ) → (∀ a b σ, tw (a + b) σ = tw a (tw b σ)) →
    (∀ b σ, wt (tw b σ) = wt σ - b) → (∀ b σ, rk (tw b σ) = rk σ) →
    (∀ b σ, (red (tw b σ)).map rkb = (red σ).map rkb) →
    ∀ (ι : Type*) (I : Finset ι) (rp : ι → Multiset Ir) (dd : ι → ℕ) (w₀ : ℤ) (t : ℕ),
      2 ≤ t → (∀ i ∈ I, 1 ≤ dd i) → (∀ i ∈ I, ∀ σ ∈ rp i, wt σ = w₀) →
      Multiset.card (((blockSum tw I rp dd).bind red).filter (fun τ => 1 < rkb τ)) = 1 →
      Multiset.card (((blockSum tw I rp dd).bind red).filter (fun τ => rkb τ = 1)) = t →
    ∀ χ₁ : Ir, rk χ₁ = 1 → wt χ₁ = w₀ - ((t : ℤ) - 1) → χ₁ ∈ blockSum tw I rp dd →
      ∃ i ∈ I, dd i = t ∧ rp i = {tw (-((t : ℤ) - 1)) χ₁}

end Formalism.NG
