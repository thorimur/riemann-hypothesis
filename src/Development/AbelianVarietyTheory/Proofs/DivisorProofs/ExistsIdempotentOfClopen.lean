import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

theorem exists_idempotent_basicOpen_eq_of_isClopen :
    ∀ (X : Scheme.{0}) (U : Set X), IsClopen U →
      ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by
  intro X U hU
  let O : Bool → X.Opens := fun i => bif i then ⟨U, hU.isOpen⟩ else ⟨Uᶜ, hU.isClosed.isOpen_compl⟩
  have hd : O true ⊓ O false = ⊥ := by
    ext x
    simp [O]
  have hcov : (⊤ : X.Opens) ≤ ⨆ i, O i := fun x _ => by
    by_cases hx : x ∈ U
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, hx⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, hx⟩
  let sf : ∀ i, Γ(X, O i) := fun i => bif i then 1 else 0
  have sub : ∀ T : X.Opens, T = ⊥ → Subsingleton Γ(X, T) := fun T hT => by
    subst hT; infer_instance
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 O sf := by
    intro i j
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' O ⊤ (fun i => homOfLE le_top) hcov sf hcompat
  obtain ⟨t, hs'⟩ : ∃ t : Γ(X, ⊤), ∀ i, X.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op t = sf i :=
    ⟨s, hs⟩
  clear hs s
  refine ⟨t, ?_, ?_⟩
  · refine X.sheaf.eq_of_locally_eq' O ⊤ (fun i => homOfLE le_top) hcov (t * t) t fun i => ?_
    have e1 : X.presheaf.map (homOfLE (le_top : O i ≤ ⊤)).op (t * t) = sf i * sf i := by
      rw [map_mul, hs' i]
    refine e1.trans (Eq.trans ?_ (hs' i).symm)
    cases i
    · exact mul_zero _
    · exact mul_one _
  · have h1 : O true ⊓ X.basicOpen t = O true := by
      rw [← Scheme.basicOpen_res, hs' true]
      exact X.basicOpen_of_isUnit isUnit_one
    have h0 : O false ⊓ X.basicOpen t = ⊥ := by
      rw [← Scheme.basicOpen_res, hs' false]
      exact X.basicOpen_zero _
    ext x
    constructor
    · intro hx
      by_contra hxU
      have : x ∈ O false ⊓ X.basicOpen t := ⟨hxU, hx⟩
      rw [h0] at this
      exact this
    · intro hx
      have : x ∈ O true := hx
      rw [← h1] at this
      exact this.2

end GlobalTheory
