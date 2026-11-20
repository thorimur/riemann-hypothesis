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
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
open Polynomial

namespace GlobalTheory

theorem charpoly_mulLeft_separable_of_adjoin_eq_top : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A]
    [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A →
    (LinearMap.mulLeft E y).charpoly.Separable := by
  intro E A _ _ _ _ _ y htop hred
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hfin : Module.finrank E A = (minpoly E y).natDegree := pb.finrank
  have hmin : minpoly E (LinearMap.mulLeft E y) = minpoly E y := by
    have h := minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective (R := E) (A := A)) y
    rw [← h]
    rfl
  have hdvd : minpoly E y ∣ (LinearMap.mulLeft E y).charpoly :=
    hmin ▸ LinearMap.minpoly_dvd_charpoly _
  have heq : (LinearMap.mulLeft E y).charpoly = minpoly E y :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (LinearMap.charpoly_monic _) hdvd
      (by rw [LinearMap.charpoly_natDegree, hfin])
  rw [heq]
  have hsq : Squarefree (minpoly E y) := (minpoly.isRadical E y).squarefree (minpoly.ne_zero hint)
  exact PerfectField.separable_iff_squarefree.mpr hsq

end GlobalTheory
