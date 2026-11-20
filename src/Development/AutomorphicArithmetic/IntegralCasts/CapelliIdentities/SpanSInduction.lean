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
import Mathlib.Topology.Sheaves.Init

noncomputable def UpperTheory.Reformulated.B.Qe24.spanS.{u_1, u_2} :
    {K : Type u_1} →
      {V : Type u_2} →
        [inst : Field K] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module K V] → (S : Subring K) → {n : ℕ} → (Fin n → V) → Submodule (↥S) V :=
    fun {K : Type u_1} {V : Type u_2} [Field K] [AddCommGroup V] [_root_.Module K V] (S : Subring K) {n : ℕ}
        (x : Fin n → V) ↦
      Submodule.span (↥S) (Set.range x)

theorem UpperTheory.Reformulated.B.Qe24.spanS_induction.{u_1, u_2} :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [StarRing K] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module K V]
      {S : Subring K} {n : ℕ} {x : Fin n → V} {p : V → Prop},
      p (0 : V) →
        (∀ (a b : V), p a → p b → p (a + b)) →
          (∀ c ∈ S, ∀ (a : V), p a → p (c • a)) → (∀ (i : Fin n), p (x i)) → ∀ v ∈ UpperTheory.Reformulated.B.Qe24.spanS S x, p v := by
  intro K V _ _ _ _ S n x p h0 hadd hsmul hx v hv
  unfold UpperTheory.Reformulated.B.Qe24.spanS at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact hx i
  | zero => exact h0
  | add a b _ _ ha hb => exact hadd a b ha hb
  | smul c a _ ha => exact hsmul c.1 c.2 a ha
