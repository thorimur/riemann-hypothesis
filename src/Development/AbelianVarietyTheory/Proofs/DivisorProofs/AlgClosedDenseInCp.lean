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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory

open Polynomial

theorem denseRange_of_isAlgClosed_padicComplex :
    ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [IsAlgClosed E] (ι : E →+* ℂ_[p]), DenseRange ι := by
  intro p _ E _ _ ι
  haveI : CharZero E := ι.charZero
  rw [Metric.denseRange_iff]
  intro z δ δpos
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) z (δ / 2) (by positivity)
  have hint : IsIntegral ℚ_[p] a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set f : ℚ_[p][X] := minpoly ℚ_[p] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have hi : DenseRange (algebraMap ℚ ℚ_[p]) := Padic.denseRange_ratCast p
  have hε : ((δ / 2) / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ / 2 := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos (half_pos δpos) (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity

  let c : PadicAlgCl p →+* ℂ_[p] := UniformSpace.Completion.coeRingHom
  have hb' : b ∈ (g.map (algebraMap ℚ (PadicAlgCl p))).roots := by
    have e : (g.map (algebraMap ℚ ℚ_[p])).map (algebraMap ℚ_[p] (PadicAlgCl p)) =
        g.map (algebraMap ℚ (PadicAlgCl p)) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    rwa [Polynomial.aroots_def, e] at hb
  have gne : g.map (algebraMap ℚ (PadicAlgCl p)) ≠ 0 := (gmon.map _).ne_zero
  have hroot : IsRoot (g.map (algebraMap ℚ (PadicAlgCl p))) b := (mem_roots gne).1 hb'
  have he : (g.map (algebraMap ℚ E)).map ι = g.map (c.comp (algebraMap ℚ (PadicAlgCl p))) := by
    rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
  have hne : (g.map (algebraMap ℚ E)).map ι ≠ 0 := ((gmon.map _).map _).ne_zero
  have hcb : c b ∈ ((g.map (algebraMap ℚ E)).map ι).roots := by
    rw [mem_roots hne, he, ← Polynomial.map_map, IsRoot, eval_map, eval₂_hom, hroot.eq_zero, map_zero]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hcb
  obtain ⟨e, -, hec⟩ := hcb
  refine ⟨e, ?_⟩
  rw [hec]
  calc dist z (c b) ≤ dist z (a : ℂ_[p]) + dist (a : ℂ_[p]) (c b) := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := by
        gcongr
        show dist (a : ℂ_[p]) (b : ℂ_[p]) < δ / 2
        rw [UniformSpace.Completion.dist_eq, dist_eq_norm]; exact hab
    _ = δ := add_halves δ

end GlobalTheory
