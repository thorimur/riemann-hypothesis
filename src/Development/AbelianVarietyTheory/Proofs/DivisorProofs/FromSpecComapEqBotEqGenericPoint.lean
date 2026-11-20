import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory

theorem fromSpec_prime_comap_bot_lies_over_genericPoint :
    ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V →
      ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime),
        P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  intro X Y _ π V hV hW P hP h
  have e := IsAffineOpen.SpecMap_appLE_fromSpec π hV hW le_rfl
  have e2 : π (hW.fromSpec ⟨P, hP⟩) =
      hV.fromSpec (Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩) := by
    have := congrArg (fun f : Spec Γ(Y, π ⁻¹ᵁ V) ⟶ X => f (⟨P, hP⟩ : PrimeSpectrum Γ(Y, π ⁻¹ᵁ V))) e
    exact this.symm
  set q : Spec Γ(X, V) := Spec.map (π.appLE V (π ⁻¹ᵁ V) le_rfl) ⟨P, hP⟩ with hqdef
  have hq : q.asIdeal = ⊥ := by
    rw [← h, Scheme.Hom.app_eq_appLE]
    rfl
  have hne : Nonempty V := ⟨⟨hV.fromSpec q, hV.range_fromSpec.subset ⟨q, rfl⟩⟩⟩
  have hgen : q = genericPoint (Spec Γ(X, V)) := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hq
  rw [e2, hgen, genericPoint_eq_of_isOpenImmersion]

end GlobalTheory
