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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace Bl.FirstBlockLemmaH

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} E V] [inst_4 : Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V] {ι : Type} [Fintype.{0} ι] [DecidableEq.{1} ι]
  {b : Module.Basis.{0, 0, 0} ι E V} {M : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) V},
  Module.Finite.{0, 0} (NumberField.RingOfIntegers.{0} E) (Subtype.{1} fun (x : V) ↦ Membership.mem.{0, 0} M x) →
    Exists.{1} fun (s : NumberField.RingOfIntegers.{0} E) ↦
      And (Membership.mem.{0, 0} (nonZeroDivisors.{0} (NumberField.RingOfIntegers.{0} E)) s)
        (∀ (v : V),
          Membership.mem.{0, 0} M v →
            ∀ (i : ι),
              Membership.mem.{0, 0}
                (RingHom.range.{0, 0} (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} E) E))
                (HMul.hMul.{0, 0, 0}
                  (DFunLike.coe.{1, 1, 1} (Algebra.algebraMap.{0, 0} (NumberField.RingOfIntegers.{0} E) E) s)
                  (DFunLike.coe.{1, 1, 1} (DFunLike.coe.{1, 1, 1} (Module.Basis.repr.{0, 0, 0} b) v) i))) := by
  intro E _ _ V _ _ _ _ ι _ _ b M hM
  obtain ⟨S, hS⟩ := Module.Finite.iff_fg.mp hM
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (NumberField.RingOfIntegers E))
    (S ×ˢ (Finset.univ : Finset ι)) (fun p : V × ι => b.repr p.1 p.2)
  refine ⟨s, s.2, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    intro i
    have h := hs (x, i) (Finset.mem_product.mpr ⟨Finset.mem_coe.mp hx, Finset.mem_univ _⟩)
    rw [IsLocalization.IsInteger, Algebra.smul_def] at h
    exact RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h)
  | zero =>
    intro i
    rw [map_zero, Finsupp.zero_apply, mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro i
    rw [map_add, Finsupp.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]
    exact mul_mem (RingHom.mem_range_self _ a) (hx i)

end Bl.FirstBlockLemmaH
