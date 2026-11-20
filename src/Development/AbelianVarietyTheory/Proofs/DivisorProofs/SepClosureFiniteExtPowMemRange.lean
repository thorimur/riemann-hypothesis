import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem sepClosure_finiteExt_pow_mem_range :
    ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L]
      [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω']
      [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω') (y : Ω'),
      ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m := by
  intro K L Ω Ω' _ _ _ _ _ _ _ _ _ _ _ _ j y
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable L Ω' := IsSepClosure.separable
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI : Algebra.IsAlgebraic K Ω' := Algebra.IsAlgebraic.trans K L Ω'
  set S := separableClosure K Ω'
  set q := ringExpChar K
  haveI : ExpChar Ω' q := expChar_of_injective_algebraMap (algebraMap K Ω').injective q
  haveI : ExpChar S q := expChar_of_injective_algebraMap (algebraMap K S).injective q
  obtain ⟨n, ⟨z, hz⟩⟩ := (isPurelyInseparable_iff_pow_mem S q).1 inferInstance y

  have hzsep : IsSeparable K (z : Ω') := mem_separableClosure_iff.1 z.2
  have hsplit : ((minpoly K (z : Ω')).map (algebraMap K Ω)).Splits :=
    IsSepClosed.splits_codomain _ hzsep
  have hroot : (((minpoly K (z : Ω')).map (algebraMap K Ω)).map (j : Ω →+* Ω')).IsRoot (z : Ω') := by
    rw [Polynomial.map_map, AlgHom.comp_algebraMap]
    simp [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  obtain ⟨x, hx⟩ := hsplit.mem_range_of_isRoot
    (Polynomial.map_ne_zero (minpoly.ne_zero hzsep.isIntegral)) hroot
  refine ⟨q ^ n, x, pow_pos (expChar_pos K q) n, ?_, fun a b => sub_pow_expChar_pow a b n⟩
  rw [← hz]
  simpa using hx.symm

end GlobalTheory.Published.AbVarRed
