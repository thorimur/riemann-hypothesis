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

namespace PI

def FiltLen : Prop :=
  ∀ (R W : Type) [CommRing R] [AddCommGroup W] [Module R W] (F : ℕ → Submodule R W) (a : ℕ),
    Antitone F → F 0 = ⊤ → F a = ⊥ →
    ∀ (V : ℕ → Type) [∀ k, AddCommGroup (V k)] [∀ k, Module R (V k)] (φ : ∀ k, W →ₗ[R] V k),
      (∀ k, ∀ x ∈ F k, φ k x = 0 → x ∈ F (k + 1)) →
      ∀ (M N : Submodule R W) (P Q : ∀ k, Submodule R (V k)), N ≤ M →
        (∀ k < a, (M ⊓ F k).map (φ k) ≤ P k) → (∀ k < a, Q k ≤ (N ⊓ F k).map (φ k)) →
        Module.length R (↥M ⧸ N.comap M.subtype) ≤
          ∑ k ∈ Finset.range a, Module.length R (↥(P k) ⧸ (Q k).comap (P k).subtype)

end PI
