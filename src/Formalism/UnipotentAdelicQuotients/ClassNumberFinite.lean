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
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
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

namespace HeckeCharacterZeroLocus

open NumberField IsDedekindDomain

def zeroLocusGL {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (R : Type) [CommRing R] [Algebra F R] : Set (GL (Fin n) R) :=
  {g | ∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) R) ij.1 ij.2) P = 0}

def IsGroupLocus {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F)) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra F R],
    1 ∈ zeroLocusGL S R ∧ (∀ g ∈ zeroLocusGL S R, ∀ h ∈ zeroLocusGL S R, g * h ∈ zeroLocusGL S R) ∧
      (∀ g ∈ zeroLocusGL S R, g⁻¹ ∈ zeroLocusGL S R)

def locusSubgroup {F : Type} [Field F] {n : ℕ} (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (R : Type) [CommRing R] [Algebra F R] : Subgroup (GL (Fin n) R) where
  carrier := zeroLocusGL S R
  one_mem' := (hS R).1
  mul_mem' := fun {a b} ha hb => (hS R).2.1 a ha b hb
  inv_mem' := fun {a} ha => (hS R).2.2 a ha

def ClassNumberFinite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F))
    (hS : IsGroupLocus S) (U : Subgroup (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))),
    IsOpen (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    IsCompact (U : Set (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F))) →
    ∃ T : Finset (locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F)),
      ∀ x : locusSubgroup S hS (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin n) F, γ ∈ zeroLocusGL S F ∧
        ∃ s ∈ T, ∃ u ∈ U,
          (x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) =
            Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ *
              (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) * ((u : locusSubgroup S hS _) : GL (Fin n) _)

end HeckeCharacterZeroLocus
