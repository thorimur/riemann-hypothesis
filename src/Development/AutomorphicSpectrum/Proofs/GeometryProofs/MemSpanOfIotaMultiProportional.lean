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
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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

namespace GlobalTheory.CompanionTheory.WedgeSpan

theorem span_of_wedge_proportional (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ)
    (b e : Fin n → V) (t : Ω) (he : LinearIndependent Ω e) (ht : t ≠ 0)
    (hbe : exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e) (i : Fin n) :
    b i ∈ Submodule.span Ω (Set.range e) := by
  classical
  by_contra hx
  have hv : LinearIndependent Ω (Fin.cons (b i) e : Fin (n + 1) → V) :=
    linearIndependent_finCons.2 ⟨he, hx⟩
  have hbe' : ExteriorAlgebra.ιMulti Ω n b = t • ExteriorAlgebra.ιMulti Ω n e := by
    have := congrArg Subtype.val hbe
    simpa using this
  have htb : Matrix.vecTail (Fin.cons (b i) b : Fin (n + 1) → V) = b :=
    by funext k; simp [Matrix.vecTail]
  have hte : Matrix.vecTail (Fin.cons (b i) e : Fin (n + 1) → V) = e :=
    by funext k; simp [Matrix.vecTail]
  have h0 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) b : Fin (n + 1) → V) = 0 :=
    (ExteriorAlgebra.ιMulti Ω (n + 1)).map_eq_zero_of_eq _ (i := 0) (j := i.succ)
      (by simp) (Fin.succ_ne_zero i).symm
  rw [ExteriorAlgebra.ιMulti_succ_apply, htb, hbe', mul_smul_comm, smul_eq_zero] at h0
  have h1 : ExteriorAlgebra.ιMulti Ω (n + 1) (Fin.cons (b i) e : Fin (n + 1) → V) = 0 := by
    rw [ExteriorAlgebra.ιMulti_succ_apply, hte]
    rcases h0 with h | h
    · exact absurd h ht
    · simpa using h
  have hfam := exteriorPower.ιMulti_family_linearIndependent_field (n := n + 1) hv
  apply hfam.ne_zero (Set.powersetCard.ofFinEmbEquiv (RelEmbedding.refl _))
  rw [exteriorPower.ιMulti_family, Equiv.symm_apply_apply]
  exact Subtype.ext h1

end GlobalTheory.CompanionTheory.WedgeSpan
