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

noncomputable section

namespace MassDataIdxRed

open Matrix

theorem isUnit_of_map {R S : Type} [CommRing R] [IsLocalRing R] [Field S] (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (h : IsUnit (π r)) : IsUnit r := by
  by_contra hr
  have hk : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  have hm : r ∈ RingHom.ker π := by
    rw [hk]; exact (IsLocalRing.mem_maximalIdeal r).2 hr
  rw [RingHom.mem_ker] at hm
  rw [hm] at h
  exact not_isUnit_zero h

def glRed {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S) :
    GL ι R →* GL ι S :=
  Units.map (π.mapMatrix : Matrix ι ι R →+* Matrix ι ι S).toMonoidHom

theorem glRed_coe {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S)
    (A : GL ι R) : ((glRed π A : GL ι S) : Matrix ι ι S) = (A : Matrix ι ι R).map π := rfl

theorem glRed_surjective {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hloc : ∀ r, IsUnit (π r) → IsUnit r) :
    Function.Surjective (glRed (ι := ι) π) := by
  intro B
  choose f hf using hπ
  set A0 : Matrix ι ι R := (B : Matrix ι ι S).map f with hA0def
  have hA0 : A0.map π = (B : Matrix ι ι S) := by
    ext i j; simp [A0, hf]
  have hdet : IsUnit A0.det := by
    apply hloc
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA0]
    exact (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  refine ⟨Matrix.nonsingInvUnit A0 hdet, ?_⟩
  apply Units.ext
  rw [glRed_coe]
  exact hA0

theorem glRed_eq_one_iff {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (A : GL ι R) :
    glRed π A = 1 ↔ ∀ i j, ((A : Matrix ι ι R) - 1) i j ∈ RingHom.ker π := by
  rw [← Units.val_inj, glRed_coe, Units.val_one]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at hij
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    ext i j
    have hij := h i j
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at hij
    rw [Matrix.map_apply, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end MassDataIdxRed
