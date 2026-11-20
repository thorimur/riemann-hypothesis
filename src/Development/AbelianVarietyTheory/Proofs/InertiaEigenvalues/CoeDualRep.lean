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

noncomputable section

namespace GlobalTheory.MonoConj

def dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := ⟨((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose,
    ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose, by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    simp [mul_inv_rev, Matrix.transpose_mul]

theorem coe_dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) (g : Γ) :
    ((dualRep r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose := rfl

end GlobalTheory.MonoConj

end
