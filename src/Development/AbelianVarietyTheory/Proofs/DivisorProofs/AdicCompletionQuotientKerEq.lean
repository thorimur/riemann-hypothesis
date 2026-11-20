import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Radical.NatInt
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

open Ideal WittVector

namespace GlobalTheory.PadicComplQuot

theorem mem_map_iff_evalOne {A : Type} [CommRing A] (I : Ideal A) (hI : I.FG) (x : AdicCompletion I A) :
    x ∈ I.map (algebraMap A (AdicCompletion I A)) ↔ AdicCompletion.evalOneₐ I x = 0 := by
  rw [← AdicCompletion.ker_evalOneₐ_eq_map _ hI, RingHom.mem_ker]
  rfl

theorem quot_completion (p : ℕ) (A : Type) [CommRing A] (_hp : IsSMulRegular A (p : A)) :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp
        (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) ∧
      RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : AdicCompletion (Ideal.span {(p : A)}) A)})).comp
        (algebraMap A (AdicCompletion (Ideal.span {(p : A)}) A))) = Ideal.span {(p : A)} := by
  set I : Ideal A := Ideal.span {(p : A)} with hIdef
  have hfg : I.FG := Submodule.fg_span_singleton _
  have hspan : Ideal.span {(p : AdicCompletion I A)} = I.map (algebraMap A (AdicCompletion I A)) := by
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  have hcomm : ∀ a : A, AdicCompletion.evalOneₐ I (algebraMap A (AdicCompletion I A) a) = Ideal.Quotient.mk I a :=
    fun a => (AdicCompletion.evalOneₐ I).commutes a
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I r)
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, hspan, mem_map_iff_evalOne I hfg, map_sub, hcomm, ha, sub_self]
  · ext a
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hspan, mem_map_iff_evalOne I hfg, hcomm,
      Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.PadicComplQuot
