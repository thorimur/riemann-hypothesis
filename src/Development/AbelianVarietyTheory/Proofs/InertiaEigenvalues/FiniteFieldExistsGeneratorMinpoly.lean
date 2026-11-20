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
open Polynomial

namespace GlobalTheory

theorem finiteField_exists_generator_minpoly (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K]
    [Algebra (ZMod l) K] :
    ∃ (a : K) (p : (ZMod l)[X]), p.Monic ∧ Irreducible p ∧ aeval a p = 0 ∧
      aeval a (derivative p) ≠ 0 ∧ (∀ y : K, ∃ q : (ZMod l)[X], aeval a q = y) ∧
      Nat.card K = l ^ p.natDegree := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : FiniteDimensional (ZMod l) K := Module.Finite.of_finite
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod l) K
  refine ⟨pb.gen, minpoly (ZMod l) pb.gen, minpoly.monic pb.isIntegral_gen,
    minpoly.irreducible pb.isIntegral_gen, minpoly.aeval _ _, ?_, ?_, ?_⟩
  · exact (Algebra.IsSeparable.isSeparable (ZMod l) pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval _ _)
  · intro y
    obtain ⟨q, -, hq⟩ := pb.exists_eq_aeval y
    exact ⟨q, hq.symm⟩
  · rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod l) (V := K), ZMod.card, pb.natDegree_minpoly,
      pb.finrank]

end GlobalTheory
