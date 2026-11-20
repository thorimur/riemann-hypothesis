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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

universe u_1 u_2 u_3 u_4

namespace GlobalTheory.RestrictScalarsSpan

theorem mul_mem_span {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4} [Field K] [Field L]
    [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) (b x : B) (hx : x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) :
    b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by
  have key : ∀ a : A, j a * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by
    intro a
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨a * i, I.mul_mem_left a hi, map_mul j a i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul l y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ l hy
  refine h.inductionOn b
    (motive := fun b => b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) ?_ ?_ ?_ ?_
  · simp
  · exact key
  · intro l b hb
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ l hb
  · intro b c hb hc
    rw [add_mul]; exact add_mem hb hc

theorem restrictScalars_map_eq_span {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4}
    [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) :
    Submodule.restrictScalars L (Ideal.map j I) =
      Submodule.span L ((⇑(AlgHom.toLinearMap j) : A → B) ''
        (↑(Submodule.restrictScalars K I) : Set A)) := by
  change _ = Submodule.span L ((j : A → B) '' (I : Set A))
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ Submodule.span B ((j : A → B) '' (I : Set A)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul b y _ hy => exact mul_mem_span h I b y hy
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Ideal.mem_map_of_mem j hi

end GlobalTheory.RestrictScalarsSpan
