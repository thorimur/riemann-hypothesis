import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.SpecificDegree
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

open NumberField Polynomial

noncomputable section

namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : F[X]) := by
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hdeg]) (by rw [hdeg]; norm_num)).2 ?_
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [mem_roots (Monic.ne_zero (by monicity!)), IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
  obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
    exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
  have := congrArg τ hr
  simp at this
  nlinarith [sq_nonneg (τ r)]

instance : Fact (Irreducible (X ^ 2 + 1 : F[X])) := ⟨irreducible_X_sq_add_one F⟩

abbrev Ext : Type := AdjoinRoot (X ^ 2 + 1 : F[X])

instance : Module.Finite F (Ext F) :=
  (AdjoinRoot.powerBasis (Monic.ne_zero (by monicity!) : (X ^ 2 + 1 : F[X]) ≠ 0)).finite

instance : NumberField (Ext F) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap F (Ext F)).injective
  to_finiteDimensional := Module.Finite.trans F (Ext F)

def ii : Ext F := AdjoinRoot.root _

theorem ii_sq : ii F ^ 2 = -1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : F[X])
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  rw [ii]; linear_combination h

def gEmb (p : F × F) : Ext F := algebraMap F (Ext F) p.1 + algebraMap F (Ext F) p.2 * ii F

end GlobalTheory.GaussExt
