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

namespace Formalism.GM

open MvPolynomial

namespace QuotientRingDecomposition

variable {R : Type} [CommRing R] {r Q : ℕ}

noncomputable def E (e : Fin r → Fin Q) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => ((e i : ℕ)))

def modQ (hQ : 0 < Q) (m : Fin r →₀ ℕ) : Fin r → Fin Q := fun i => ⟨m i % Q, Nat.mod_lt _ hQ⟩

noncomputable def divQ (Q : ℕ) (m : Fin r →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i / Q)

@[simp] lemma E_apply (e : Fin r → Fin Q) (i : Fin r) : E e i = (e i : ℕ) := rfl

@[simp] lemma divQ_apply (m : Fin r →₀ ℕ) (i : Fin r) : divQ Q m i = m i / Q := rfl

lemma decomp (hQ : 0 < Q) (m : Fin r →₀ ℕ) : E (modQ hQ m) + Q • divQ Q m = m := by
  ext i
  simp [modQ, Nat.mod_add_div]

end QuotientRingDecomposition

end Formalism.GM
