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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

abbrev addJ {K : Type} (J : K → Type) (N : ℕ) : Unit ⊕ K → Type := Sum.elim (fun _ => Fin (N + 1)) J

instance addJ_fintype {K : Type} (J : K → Type) [∀ k, Fintype (J k)] (N : ℕ) : ∀ k, Fintype (addJ J N k)
  | .inl _ => inferInstanceAs (Fintype (Fin (N + 1)))
  | .inr k => inferInstanceAs (Fintype (J k))

def addY {K : Type} {J : K → Type} {N : ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (y : (Σ k, J k) → Ω₀) (x' : Fin (N + 1) → Ω) : (Σ k, addJ J N k) → Ω
  | ⟨.inl _, a⟩ => x' a
  | ⟨.inr k, a⟩ => algebraMap Ω₀ Ω (y ⟨k, a⟩)

def addV {K : Type} (J : K → Type) (N : ℕ) : (Σ k, J k) → Σ k, addJ J N k := fun p => ⟨.inr p.1, p.2⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
