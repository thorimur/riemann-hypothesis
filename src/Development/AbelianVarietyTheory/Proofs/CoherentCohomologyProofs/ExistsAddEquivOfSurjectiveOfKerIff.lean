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

namespace GlobalTheory.AddEquivOfSurjectiveKernel

universe u_1 u_2 u_3

theorem exists_addEquiv_of_surjective_of_ker_iff {A : Type u_1} {B : Type u_2} {C : Type u_3}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (f : A →+ B) (g : A →+ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : ∀ a : A, f a = 0 ↔ g a = 0) :
    ∃ e : B ≃+ C, ∀ a : A, e (f a) = g a := by
  have key : ∀ a b : A, f a = f b ↔ g a = g b := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, h, map_sub, sub_eq_zero]
  choose s hs using hf
  choose t ht using hg
  have h1 : ∀ a, g (s (f a)) = g a := fun a => (key _ _).1 (hs _)
  have h2 : ∀ a, f (t (g a)) = f a := fun a => (key _ _).2 (ht _)
  refine ⟨{ toFun := fun b => g (s b)
            invFun := fun c => f (t c)
            left_inv := fun b => by
              show f (t (g (s b))) = b
              rw [h2, hs]
            right_inv := fun c => by
              show g (s (f (t c))) = c
              rw [h1, ht]
            map_add' := fun x y => by
              show g (s (x + y)) = g (s x) + g (s y)
              rw [← map_add, ← key, map_add, hs, hs, hs] }, fun a => h1 a⟩

end GlobalTheory.AddEquivOfSurjectiveKernel
