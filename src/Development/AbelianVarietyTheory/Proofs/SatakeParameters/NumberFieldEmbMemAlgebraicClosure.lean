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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory

open IntermediateField

theorem numberField_emb_mem_algebraicClosure {LL : Type} [Field LL] [NumberField LL]
    (e : LL →+* ℂ) (z : LL) : e z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  have hz : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
  simpa using hz.algHom e.toRatAlgHom

theorem padic_emb_extends_algebraicClosure (p : ℕ) [Fact p.Prime] (LL : Type) [Field LL]
    [NumberField LL] (e : LL →+* ℂ) (i : LL →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p],
      ∀ (z : LL) (hz : e z ∈ algebraicClosure ℚ ℂ), i z = lam ⟨e z, hz⟩ := by
  let e' : LL →+* algebraicClosure ℚ ℂ :=
    (e.codRestrict (algebraicClosure ℚ ℂ).toSubring
      (fun z => numberField_emb_mem_algebraicClosure e z))
  letI : Algebra LL (algebraicClosure ℚ ℂ) := e'.toAlgebra
  letI : Algebra LL ℂ_[p] := i.toAlgebra
  haveI : IsScalarTower ℚ LL (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (RingHom.congr_fun (Subsingleton.elim ((algebraMap LL (algebraicClosure ℚ ℂ)).comp
        (algebraMap ℚ LL)) (algebraMap ℚ (algebraicClosure ℚ ℂ))) x).symm)
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic LL (algebraicClosure ℚ ℂ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) LL
  let lamA : algebraicClosure ℚ ℂ →ₐ[LL] ℂ_[p] := IsAlgClosed.lift
  refine ⟨lamA.toRingHom, fun z hz => ?_⟩
  have h1 : (⟨e z, hz⟩ : algebraicClosure ℚ ℂ) = algebraMap LL (algebraicClosure ℚ ℂ) z := rfl
  rw [h1]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end GlobalTheory
