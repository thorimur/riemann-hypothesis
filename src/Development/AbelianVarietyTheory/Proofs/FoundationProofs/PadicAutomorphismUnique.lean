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
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

open Polynomial

theorem denseRange_of_isAlgClosed_padicAlgCl (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) : DenseRange j := by
  rw [Metric.denseRange_iff]
  intro a δ δpos
  haveI : CharZero Ω := j.charZero
  have hint : IsIntegral ℚ_[l] a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set f : ℚ_[l][X] := minpoly ℚ_[l] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have hi : DenseRange (algebraMap ℚ ℚ_[l]) := Padic.denseRange_ratCast l
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have he : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l))
      = (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, he, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨c, -, hc⟩ := hb
  exact ⟨c, by rw [hc, dist_eq_norm]; exact hab⟩

theorem padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l)
      (σ τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), (∀ x, σ (j x) = τ (j x)) → σ = τ := by
  intro l _ Ω _ _ j σ τ h
  have hc : ∀ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm (g : PadicAlgCl l →+* PadicAlgCl l)
      fun x => (spectralNorm_eq_of_equiv g x).symm).continuous
  have := (denseRange_of_isAlgClosed_padicAlgCl l Ω j).equalizer (hc σ) (hc τ) (funext h)
  exact AlgEquiv.ext fun x => congrFun this x

end GlobalTheory
