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

namespace GlobalTheory

open Polynomial in
theorem no_order_l_of_cyclotomic_irreducible :
    ∀ (E : Type) [Field E] [CharZero E] (l N : ℕ) (g : Matrix (Fin N) (Fin N) E),
      l.Prime → Irreducible (Polynomial.cyclotomic l E) → N + 1 < l → g ^ l = 1 → g = 1 := by
  intro E _ _ l N g hl hirr hN hg
  haveI : Fact l.Prime := ⟨hl⟩
  have hmon : g.charpoly.Monic := Matrix.charpoly_monic g
  have hdeg : g.charpoly.natDegree = N := by
    simpa using Matrix.charpoly_natDegree_eq_dim g
  have hndvd : ¬ cyclotomic l E ∣ g.charpoly := by
    intro h
    have h1 := Polynomial.natDegree_le_of_dvd h hmon.ne_zero
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl, hdeg] at h1
    omega
  obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).2 hndvd
  have hev := congrArg (aeval g) hab
  simp only [map_add, map_mul, map_one, Matrix.aeval_self_charpoly, mul_zero, add_zero] at hev
  have hcyc : aeval g (cyclotomic l E) * (g - 1) = 0 := by
    have := congrArg (aeval g) (Polynomial.cyclotomic_prime_mul_X_sub_one E l)
    simp only [map_mul, map_sub, aeval_X, map_one, map_pow] at this
    rw [this, hg, sub_self]
  have : g - 1 = 0 := by
    calc g - 1 = (aeval g a * aeval g (cyclotomic l E)) * (g - 1) := by rw [hev, one_mul]
      _ = aeval g a * (aeval g (cyclotomic l E) * (g - 1)) := by rw [mul_assoc]
      _ = 0 := by rw [hcyc, mul_zero]
  exact sub_eq_zero.1 this

end GlobalTheory
