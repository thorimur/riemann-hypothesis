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

universe u_1

namespace Bl.MatrixMapSub

theorem goal1 :
  ∀ {A : Type u_1} [inst : CommRing.{u_1} A] {d : Nat} (σ : RingHom.{u_1, u_1} A A)
  (X Y : Matrix.{0, 0, u_1} (Fin d) (Fin d) A),
  Eq.{u_1 + 1}
    (Matrix.map.{u_1, u_1, 0, 0} (HSub.hSub.{u_1, u_1, u_1} X Y) (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
    (HSub.hSub.{u_1, u_1, u_1} (Matrix.map.{u_1, u_1, 0, 0} X (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))
      (Matrix.map.{u_1, u_1, 0, 0} Y (DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1} σ))) := by
  intro A _ d σ X Y
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

end Bl.MatrixMapSub
