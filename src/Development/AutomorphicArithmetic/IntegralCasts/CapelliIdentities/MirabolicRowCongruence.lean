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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.mirabolic_row_congruence :
    ∀ {R : Type} [CommRing R] (I J : Ideal R) (g : GL (Fin 2) R), I ≤ J →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g : GL (Fin 2) (R ⧸ I)) : Matrix (Fin 2) (Fin 2) (R ⧸ I)) = ![0, 1] →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) g : GL (Fin 2) (R ⧸ J)) : Matrix (Fin 2) (Fin 2) (R ⧸ J)) = ![0, 1] := by
  intro R _ I J g hIJ h
  have key : ∀ (K : Ideal R) (j : Fin 2),
      Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk K) g :
        GL (Fin 2) (R ⧸ K)) : Matrix (Fin 2) (Fin 2) (R ⧸ K)) j
        = Ideal.Quotient.mk K ((g : Matrix (Fin 2) (Fin 2) R) 1 j) := by
    intro K j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map]
  funext j
  have hj := congrArg (Ideal.Quotient.factor hIJ) ((key I j).symm.trans (congrFun h j))
  rw [Ideal.Quotient.factor_mk] at hj
  rw [key J j, hj]
  fin_cases j <;> simp
