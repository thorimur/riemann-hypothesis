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

namespace MassDataIdxCore

open Matrix

theorem reindex_gl {H R : Type} [Group H] [CommRing R] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (e : n ≃ ι) (I : Ideal R) (Q : H → Prop) (ψ : H →* GL n R) (hψ : Function.Surjective ψ)
    (hQ : ∀ h, (∀ i j, (((ψ h : GL n R) : Matrix n n R) - 1) i j ∈ I) ↔ Q h) :
    ∃ ψ' : H →* GL ι R, Function.Surjective ψ' ∧
      ∀ h, (∀ i j, (((ψ' h : GL ι R) : Matrix ι ι R) - 1) i j ∈ I) ↔ Q h := by
  classical
  let φ : GL n R ≃* GL ι R := Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv
  refine ⟨φ.toMonoidHom.comp ψ, φ.surjective.comp hψ, fun h => ?_⟩
  rw [← hQ h]
  have key : ∀ i j, (((φ.toMonoidHom.comp ψ h : GL ι R) : Matrix ι ι R) - 1) i j =
      (((ψ h : GL n R) : Matrix n n R) - 1) (e.symm i) (e.symm j) := by
    intro i j
    simp [φ, Matrix.sub_apply, Matrix.one_apply, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  simp only [key]
  constructor
  · intro H i j
    simpa using H (e i) (e j)
  · intro H i j
    exact H _ _

end MassDataIdxCore
