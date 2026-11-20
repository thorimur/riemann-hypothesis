import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Scheme
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
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

theorem isField_of_spec_singleton_stalk_isField :
    ∀ (R : CommRingCat.{0}) (q : Spec R), (∀ q' : Spec R, q' = q) →
      IsField ((Spec R).presheaf.stalk q) → IsField R := by
  intro R q huniq hfield
  letI : Algebra R ((Spec R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  haveI : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) q
  haveI hloc : IsLocalization.AtPrime ((Spec R).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  have hunit : ∀ x : R, x ∉ q.asIdeal → IsUnit x := by
    intro x hx
    by_contra hxu
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hxu
    have h1 : ((⟨m, hm.isPrime⟩ : PrimeSpectrum R) : Spec R) = q := huniq _
    have hmq : m = q.asIdeal := by
      rw [← h1]
    exact hx (hmq ▸ hxm)
  let e : R ≃ₐ[R] ((Spec R).presheaf.stalk q) :=
    IsLocalization.atUnits R q.asIdeal.primeCompl (S := (Spec R).presheaf.stalk q)
      (fun y hy => (IsUnit.mem_submonoid_iff y).2 (hunit y hy))
  exact MulEquiv.isField hfield e.toMulEquiv

end GlobalTheory
