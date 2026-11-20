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

namespace ReciprocityTheory.ChartRestriction.G.T0

def RegLaw {Λ Wt : Type*} (Forms : Wt → Type*) (Pt Pt' : Λ → Type*)
    (emb : ∀ la, Pt la → Pt' la) (v : ∀ la, Pt' la → ∀ {w : Wt}, Forms w → EReal)
    (Q : Type*) (ord : Q → ∀ {w : Wt}, Forms w → EReal)
    (NoZero : ∀ {w : Wt} {n : ℕ}, (Fin n → Forms w) → Prop) : Prop :=

  (∀ (w : Wt) (F : Forms w),
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) F) →
      (∀ la (y' : Pt' la), 0 ≤ v la y' F) ∧ ∀ q : Q, 0 ≤ ord q F) ∧

  (∀ (wL wE : Wt) (n : ℕ) (ws : Fin n → Forms wL) (et : Forms wE) (nu : Λ → ℝ) (c' : ℝ),
    0 ≤ c' → NoZero ws →
    (∀ la (y : Pt la), 0 ≤ v la (emb la y) et ∧ (v la (emb la y) et ≠ ⊤ →
      (⨅ k, v la (emb la y) (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la (emb la y) et)) →
    (∀ la (y' : Pt' la), 0 ≤ v la y' et ∧ (v la y' et ≠ ⊤ →
      (⨅ k, v la y' (ws k)) ≤ (nu la : EReal) + (c' : EReal) * v la y' et)) ∧
    ∀ q : Q, 0 ≤ ord q et ∧ (ord q et ≠ ⊤ → (⨅ k, ord q (ws k)) ≤ (c' : EReal) * ord q et))

end ReciprocityTheory.ChartRestriction.G.T0
