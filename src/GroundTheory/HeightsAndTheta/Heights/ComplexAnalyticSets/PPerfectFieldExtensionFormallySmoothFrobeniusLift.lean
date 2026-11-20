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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

section FrobeniusLift

variable {C : Type*} [CommRing C] {N : Ideal C} {p : ℕ}

theorem pow_prime_add_of_sq_eq_bot (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) (c : C) {n : C}
    (hn : n ∈ N) : (c + n) ^ p = c ^ p := by
  have hn2 : n ^ 2 = 0 := by
    have := Ideal.pow_mem_pow hn 2
    rwa [hN, Ideal.mem_bot] at this
  have hnp : n ^ p = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp.two_le
    rw [hk, pow_add, hn2, zero_mul]
  rw [add_pow_prime_eq hp, hpC, hnp]
  simp

theorem pow_prime_eq_of_mk_eq (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) {c c' : C}
    (h : Ideal.Quotient.mk N c = Ideal.Quotient.mk N c') : c ^ p = c' ^ p := by
  have hmem : c - c' ∈ N := Ideal.Quotient.eq.mp h
  have := pow_prime_add_of_sq_eq_bot hp hpC hN c' hmem
  rwa [add_sub_cancel] at this

noncomputable def sqZeroFrobeniusLift (N : Ideal C) (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) :
    C ⧸ N →+* C where
  toFun y := (Ideal.Quotient.mk_surjective y).choose ^ p
  map_one' := by
    rw [pow_prime_eq_of_mk_eq hp hpC hN (c' := 1) (by rw [(Ideal.Quotient.mk_surjective _).choose_spec,
      map_one]), one_pow]
  map_mul' x y := by
    rw [← mul_pow]
    exact pow_prime_eq_of_mk_eq hp hpC hN (by simp only [map_mul, (Ideal.Quotient.mk_surjective _).choose_spec])
  map_zero' := by
    rw [pow_prime_eq_of_mk_eq hp hpC hN (c' := 0) (by rw [(Ideal.Quotient.mk_surjective _).choose_spec,
      map_zero]), zero_pow hp.ne_zero]
  map_add' x y := by
    have hadd : ((Ideal.Quotient.mk_surjective x).choose + (Ideal.Quotient.mk_surjective y).choose) ^ p =
        (Ideal.Quotient.mk_surjective x).choose ^ p + (Ideal.Quotient.mk_surjective y).choose ^ p := by
      rw [add_pow_prime_eq hp, hpC]; simp
    rw [← hadd]
    exact pow_prime_eq_of_mk_eq hp hpC hN (by simp only [map_add, (Ideal.Quotient.mk_surjective _).choose_spec])

theorem sqZeroFrobeniusLift_mk (hp : p.Prime) (hpC : (p : C) = 0) (hN : N ^ 2 = ⊥) (c : C) :
    sqZeroFrobeniusLift N hp hpC hN (Ideal.Quotient.mk N c) = c ^ p :=
  pow_prime_eq_of_mk_eq hp hpC hN (Ideal.Quotient.mk_surjective _).choose_spec

end FrobeniusLift

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
