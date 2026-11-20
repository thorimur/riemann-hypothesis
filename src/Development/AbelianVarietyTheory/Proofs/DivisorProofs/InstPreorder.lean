import Mathlib.Algebra.Colimit.Ring
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

open IsLocalRing

noncomputable section

namespace GlobalTheory.Henselisation

variable (R : Type) [CommRing R] [IsLocalRing R]

structure EtNbhd where

  n : ℕ

  I : Ideal (MvPolynomial (Fin n) R)

  etale : Algebra.Etale R (MvPolynomial (Fin n) R ⧸ I)

  pt : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] ResidueField R

namespace EtNbhd

variable {R}

abbrev A (i : EtNbhd R) : Type := MvPolynomial (Fin i.n) R ⧸ i.I

instance (i : EtNbhd R) : Algebra.Etale R i.A := i.etale

def q (i : EtNbhd R) : Ideal i.A := RingHom.ker i.pt

instance (i : EtNbhd R) : i.q.IsPrime := RingHom.ker_isPrime _

abbrev B (i : EtNbhd R) : Type := Localization.AtPrime i.q

instance : Preorder (EtNbhd R) where
  le i j := ∃ f : i.A →ₐ[R] j.A, j.pt.comp f = i.pt
  le_refl i := ⟨AlgHom.id R i.A, AlgHom.comp_id _⟩
  le_trans i j k := fun ⟨f, hf⟩ ⟨g, hg⟩ => ⟨g.comp f, by rw [← AlgHom.comp_assoc, hg, hf]⟩

theorem q_eq_comap {i j : EtNbhd R} (f : i.A →ₐ[R] j.A) (hf : j.pt.comp f = i.pt) :
    i.q = j.q.comap (f : i.A →+* j.A) := by
  ext a
  simp only [q, RingHom.mem_ker, Ideal.mem_comap]
  rw [← hf]
  rfl

noncomputable def trans {i j : EtNbhd R} (h : i ≤ j) : i.B →+* j.B :=
  Localization.localRingHom i.q j.q (h.choose : i.A →+* j.A) (q_eq_comap _ h.choose_spec)

noncomputable def base : EtNbhd R where
  n := 0
  I := RingHom.ker (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom
  etale := Algebra.Etale.of_equiv (Ideal.quotientKerAlgEquivOfSurjective
    (f := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom)
    (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).surjective).symm
  pt := (IsScalarTower.toAlgHom R R (ResidueField R)).comp
    (Ideal.quotientKerAlgEquivOfSurjective (f := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom)
      (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).surjective).toAlgHom

instance : Nonempty (EtNbhd R) := ⟨base⟩

end EtNbhd

def Hens : Type :=
  Ring.DirectLimit (fun i : EtNbhd R => i.B) (fun _ _ h => ⇑(EtNbhd.trans h))

noncomputable instance : CommRing (Hens R) :=
  inferInstanceAs (CommRing (Ring.DirectLimit (fun i : EtNbhd R => i.B) (fun _ _ h => ⇑(EtNbhd.trans h))))

variable {R}

noncomputable def Hens.of (i : EtNbhd R) : i.B →+* Hens R :=
  Ring.DirectLimit.of (fun i : EtNbhd R => i.B) (fun _ _ h => ⇑(EtNbhd.trans h)) i

variable (R) in

noncomputable instance : Algebra R (Hens R) :=
  ((Hens.of (EtNbhd.base (R := R))).comp (algebraMap R (EtNbhd.base (R := R)).B)).toAlgebra

end GlobalTheory.Henselisation

end
