import Mathlib.Algebra.DualNumber
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

namespace Bl.ThirdBlockLemmaB

noncomputable def goal1 :
  {S : Type} →   [inst : CommRing S] →     {A A' : Type} →       [inst_1 : CommRing A] →         [inst_2 : Algebra S A] →           [inst_3 : CommRing A'] → [inst_4 : Algebra S A'] → AlgHom S A A' → AlgHom S (DualNumber A) (DualNumber A') :=
  fun {S} _ {A A'} _ _ _ _ φ =>
    TrivSqZeroExt.lift ((TrivSqZeroExt.inlAlgHom S A' A').comp φ)
      (((TrivSqZeroExt.inrHom A' A').restrictScalars S).comp φ.toLinearMap)
      (fun x y => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inr_mul_inr])
      (fun r x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, map_mul])
      (fun r x => by
        simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, LinearMap.coe_restrictScalars, TrivSqZeroExt.inrHom_apply, AlgHom.coe_comp, TrivSqZeroExt.inlAlgHom_apply, TrivSqZeroExt.inr_mul_inl, op_smul_eq_mul, map_mul])

end Bl.ThirdBlockLemmaB
