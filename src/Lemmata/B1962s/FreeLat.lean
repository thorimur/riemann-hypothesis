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
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ENatToNat
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

noncomputable def Bl.FreeLattices.FreeLat :
  Prop :=
  ∀ (p : Nat) [inst : Fact (Nat.Prime p)] (σ : Type) (L : Submodule.{0, 0} (PadicInt p) (MvPolynomial.{0, 0} σ (Padic p)))
    (W : Submodule.{0, 0} (Padic p) (MvPolynomial.{0, 0} σ (Padic p))),
    FiniteDimensional.{0, 0} (Padic p)
        (Subtype.{1} fun (x : MvPolynomial.{0, 0} σ (Padic p)) ↦ Membership.mem.{0, 0} W x) →
      (∀ (x : MvPolynomial.{0, 0} σ (Padic p)), Membership.mem.{0, 0} L x → Membership.mem.{0, 0} W x) →
        Submodule.FG.{0, 0} L →
          Exists.{1} fun (m : Nat) ↦
            Exists.{1} fun (f : Fin m → MvPolynomial.{0, 0} σ (Padic p)) ↦
              And (∀ (a : Fin m), Membership.mem.{0, 0} L (f a))
                (And (LinearIndependent.{0, 0, 0} (PadicInt p) f)
                  (Eq.{1} (Submodule.span.{0, 0} (PadicInt p) (Set.range.{0, 1} f)) L))

namespace Bl.FreeLattices

private theorem tf (p : Nat) [Fact (Nat.Prime p)] (σ : Type) :
    Module.IsTorsionFree (PadicInt p) (MvPolynomial σ (Padic p)) := by
  refine Module.IsTorsionFree.comap (S := Padic p) (algebraMap (PadicInt p) (Padic p)) ?_ ?_
  · intro r hr
    have h0 : r ≠ 0 := hr.ne_zero
    have h1 : algebraMap (PadicInt p) (Padic p) r ≠ 0 := by
      simpa using h0
    exact IsRegular.of_ne_zero h1
  · intro r m
    exact algebraMap_smul (Padic p) r m

theorem goal1 :
  Bl.FreeLattices.FreeLat := by
  intro p _ σ L W _ _ hL
  have := tf p σ
  have : Module.Finite (PadicInt p) L := Module.Finite.iff_fg.mpr hL
  let b := Module.finBasis (PadicInt p) L
  refine ⟨Module.finrank (PadicInt p) L, fun i => (b i : MvPolynomial σ (Padic p)), ?_, ?_, ?_⟩
  · intro a
    exact (b a).2
  · exact b.linearIndependent.map' L.subtype L.ker_subtype
  · have h := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h

end Bl.FreeLattices
