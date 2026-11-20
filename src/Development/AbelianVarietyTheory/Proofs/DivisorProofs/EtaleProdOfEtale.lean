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
import Mathlib.RingTheory.Etale.Pi
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

namespace GlobalTheory.EtaleProd

abbrev fam (A₁ A₂ : Type) : Fin 2 → Type := ![A₁, A₂]

instance instCommRing (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] : ∀ i, CommRing (fam A₁ A₂ i) :=
  Fin.cases (inferInstanceAs (CommRing A₁)) (Fin.cases (inferInstanceAs (CommRing A₂)) finZeroElim)

instance instAlgebra (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] :
    ∀ i, Algebra B (fam A₁ A₂ i) :=
  Fin.cases (inferInstanceAs (Algebra B A₁)) (Fin.cases (inferInstanceAs (Algebra B A₂)) finZeroElim)

theorem etale_fam (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂]
    (h₁ : Algebra.Etale B A₁) (h₂ : Algebra.Etale B A₂) : ∀ i, Algebra.Etale B (fam A₁ A₂ i) :=
  Fin.cases h₁ (Fin.cases h₂ finZeroElim)

end GlobalTheory.EtaleProd

open GlobalTheory.EtaleProd in

theorem GlobalTheory.etale_prod : ∀ (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂], Algebra.Etale B A₁ → Algebra.Etale B A₂ → Algebra.Etale B (A₁ × A₂) := by
  intro B A₁ A₂ _ _ _ _ _ h₁ h₂
  haveI := etale_fam B A₁ A₂ h₁ h₂
  exact Algebra.Etale.of_equiv
    (AlgEquiv.ofRingEquiv (R := B) (f := RingEquiv.piFinTwo (fam A₁ A₂)) fun _ => rfl)
