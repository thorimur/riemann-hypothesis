import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LineDeriv.Basic
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
import Mathlib.Topology.Sheaves.Init
open Matrix

namespace PositivityTheory.Xgp.gram_grad

theorem triple_deriv {n k : ℕ} (G : ℝ → Matrix (Fin n) (Fin n) ℂ) (V : ℝ → Matrix (Fin n) (Fin k) ℂ)
    (G' : Matrix (Fin n) (Fin n) ℂ) (V' : Matrix (Fin n) (Fin k) ℂ) (t : ℝ)
    (hG : ∀ p q, HasDerivAt (fun s => G s p q) (G' p q) t)
    (hV : ∀ p q, HasDerivAt (fun s => V s p q) (V' p q) t) (p q : Fin k) :
    HasDerivAt (fun s => ((V s)ᴴ * G s * V s) p q)
      ((V'ᴴ * G t * V t + (V t)ᴴ * G' * V t + (V t)ᴴ * G t * V') p q) t := by
  have h : HasDerivAt (fun s => ∑ j, (∑ i, star (V s i p) * G s i j) * V s j q)
      (∑ j, ((∑ i, (star (V' i p) * G t i j + star (V t i p) * G' i j)) * V t j q +
        (∑ i, star (V t i p) * G t i j) * V' j q)) t := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    refine HasDerivAt.fun_mul ?_ (hV j q)
    refine HasDerivAt.fun_sum fun i _ => ?_
    exact HasDerivAt.fun_mul (hV i p).star (hG i j)
  convert h using 1
  · funext s
    simp only [Matrix.mul_apply, conjTranspose_apply]
  · simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_add_distrib, add_mul]

theorem line_deriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (x : E) (hf : DifferentiableAt ℝ f x) (v : E) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f x v) 0 :=
  hf.hasFDerivAt.hasLineDerivAt v

end PositivityTheory.Xgp.gram_grad
