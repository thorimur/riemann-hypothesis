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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf25.modFun :
    {O M ι : Type} → [inst : CommRing O] → [inst_1 : AddCommGroup M] → [_root_.Module O M] → _root_.Module O (ι → M) :=
    fun {O M ι : Type} [CommRing O] [AddCommGroup M] [_root_.Module O M] ↦ Pi.Function.module ι O M
attribute [local instance] UpperTheory.Reformulated.B.Qf25.modFun

theorem UpperTheory.Reformulated.B.Qf25.trace_zero :
    ∀ {k : Type} [inst : Field k] (S T : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) k),
      T.det ≠ (0 : k) →
        S.charpoly.Separable →
          ∀ (v : Fin (2 : ℕ) → k),
            v ≠ (0 : Fin (2 : ℕ) → k) →
              T.mulVec v ∉ k ∙ v →
                ∀ (a b c : k),
                  S.mulVec v = a • v →
                    S.mulVec (T.mulVec v) = b • T.mulVec v →
                      S.mulVec (T.mulVec (T.mulVec v)) = c • T.mulVec (T.mulVec v) → T.trace = (0 : k) := by
  intro k _ S T hdet hsep v hv hw a b c ha hb hc
  have hCH : T.mulVec (T.mulVec v) = T.trace • T.mulVec v - T.det • v := by
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.trace_fin_two,
        Matrix.det_fin_two] <;> ring
  generalize T.mulVec v = w at hw hb hc hCH
  have hD : v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    intro h
    apply hw
    rw [Submodule.mem_span_singleton]
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i
        · exact h0
        · exact h1
      have hw0 : w 0 = 0 := by
        have : v 1 * w 0 = 0 := by linear_combination -h + w 1 * h0
        exact (mul_eq_zero.1 this).resolve_left h1
      refine ⟨w 1 / v 1, ?_⟩
      ext i
      fin_cases i
      · simp [h0, hw0]
      · simp [h1]
    · refine ⟨w 0 / v 0, ?_⟩
      ext i
      fin_cases i
      · simp [h0]
      · show w 0 / v 0 * v 1 = w 1
        field_simp
        linear_combination -h
  rw [hCH, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb] at hc
  have c0 : T.trace * (b * w 0) - T.det * (a * v 0) = c * (T.trace * w 0 - T.det * v 0) :=
    congrFun hc 0
  have c1 : T.trace * (b * w 1) - T.det * (a * v 1) = c * (T.trace * w 1 - T.det * v 1) :=
    congrFun hc 1
  by_contra ht
  have hac : a = c := by
    have : T.det * (a - c) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination w 0 * c1 - w 1 * c0
    exact sub_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)).resolve_left hdet)
  have hbc : b = c := by
    have : T.trace * (b - c) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination v 0 * c1 - v 1 * c0
    exact sub_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)).resolve_left ht)
  subst hac hbc
  have a0 := congrFun ha 0
  have a1 := congrFun ha 1
  have b0 := congrFun hb 0
  have b1 := congrFun hb 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    at a0 a1 b0 b1
  have s00 : S 0 0 = b := by
    apply mul_right_cancel₀ hD
    linear_combination w 1 * a0 - v 1 * b0
  have s01 : S 0 1 = 0 := by
    apply mul_right_cancel₀ hD
    linear_combination v 0 * b0 - w 0 * a0
  have s11 : S 1 1 = b := by
    apply mul_right_cancel₀ hD
    linear_combination v 0 * b1 - w 0 * a1
  have hp : S.charpoly = (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C b) := by
    rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, s00, s01, s11]
    simp only [map_add, map_sub, map_mul, map_zero]
    ring
  have hu := hsep.squarefree (Polynomial.X - Polynomial.C b) (hp ▸ dvd_rfl)
  exact Polynomial.not_isUnit_X_sub_C b hu
