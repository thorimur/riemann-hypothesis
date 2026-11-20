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

namespace GlobalTheory.IsolatedTheoremFive

theorem main {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n d : ℕ}
    (E : Matrix (Fin n) (Fin d) K) (h : Function.Injective (Matrix.mulVec E)) :
    Function.Injective (Matrix.mulVec (Matrix.map E (⇑φ : K → K'))) := by
  have hl : LinearMap.ker (Matrix.mulVecLin E) = ⊥ := LinearMap.ker_eq_bot.mpr h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin E) hl
  have hB : LinearMap.toMatrix' g * E = 1 := by
    have e : Matrix.mulVecLin E = Matrix.toLin' E := rfl
    have : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin E) = LinearMap.toMatrix' g * E := by
      rw [LinearMap.toMatrix'_comp, e, LinearMap.toMatrix'_toLin']
    rw [← this, hg, LinearMap.toMatrix'_id]
  have hB' : (LinearMap.toMatrix' g).map φ * E.map φ = 1 := by
    rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero φ) (map_one φ)]
  intro x y hxy
  have := congrArg (Matrix.mulVec ((LinearMap.toMatrix' g).map φ)) hxy
  simpa [Matrix.mulVec_mulVec, hB'] using this

theorem target : ∀ {K K' : Type} [inst : Field K] [inst_1 : Field K'] (φ : K →+* K') {n d : ℕ} (E : Matrix (Fin n) (Fin d) K), Function.Injective (Matrix.mulVec E) → Function.Injective (Matrix.mulVec (Matrix.map E (⇑φ : K → K'))) := by
  intro K K' _ _ φ n d E h
  exact main φ E h

end GlobalTheory.IsolatedTheoremFive
