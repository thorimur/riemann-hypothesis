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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimitiveFormRemainder.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (N : ℕ) (δ : (Fin d → ℂ) → ℂ) (q : σ → Fin N → (Fin d → ℂ) → ℂ) (n : σ → ℕ)
    (c : (i : σ) → Fin (n i) → (Fin d → ℂ) → ℂ) (f : (σ → ℂ) → ℂ),
    AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) → (∀ i j, AnalyticAt ℂ (c i j) (A w)) →
    (∀ i (T : ℂ), T ^ n i + ∑ j, c i j (A w) * T ^ (j : ℕ) = (T - w i) ^ n i) →
    AnalyticAt ℂ f w →
    ∃ (M : ℕ) (R : Polynomial ((Fin d → ℂ) → ℂ)), (∀ k, AnalyticAt ℂ (R.coeff k) (A w)) ∧
      ∀ᶠ z in 𝓝 w, (∀ i, z i ^ n i + ∑ j, c i j (A z) * z i ^ (j : ℕ) = 0) →
        (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
        δ (A z) ^ M * f z = R.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
