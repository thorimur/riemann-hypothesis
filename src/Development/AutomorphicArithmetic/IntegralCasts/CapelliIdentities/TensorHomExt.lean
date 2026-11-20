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

theorem UpperTheory.Reformulated.B.Qk54.tensor_hom_ext :
    ∀ {A A' C Ω : Type}
    [inst : CommRing A] [inst_1 : CommRing A'] [inst_2 : CommRing C] [inst_3 : Algebra A A'] [inst_4 : Algebra A C]
    [inst_5 : CommRing Ω] {u v : TensorProduct A C A' →+* Ω},
    (∀ (c : C), (u : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A')) = (v : TensorProduct A C A' → Ω) (c ⊗ₜ[A] (1 : A'))) →
      (∀ (b : A'), (u : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b) = (v : TensorProduct A C A' → Ω) ((1 : C) ⊗ₜ[A] b)) →
        u = v := by
  intro A A' C Ω _ _ _ _ _ _ u v h₁ h₂
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c b =>
    have e : c ⊗ₜ[A] b = (c ⊗ₜ[A] (1 : A')) * ((1 : C) ⊗ₜ[A] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
