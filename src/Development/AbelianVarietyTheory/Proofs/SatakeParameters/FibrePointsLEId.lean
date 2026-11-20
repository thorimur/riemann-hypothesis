import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

def FibrePointsLE {Z X : Scheme.{0}} (f : Z ⟶ X) (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) (s : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z)),
    (∀ j, s j ≫ f = y) → ¬ Function.Injective s

def diagCompl {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (pullback f f).Opens :=
  ⟨(Set.range (pullback.diagonal f))ᶜ, (pullback.diagonal f).isClosedEmbedding.isClosed_range.isOpen_compl⟩

def diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsSeparated f] : (diagCompl f).toScheme ⟶ Z :=
  (diagCompl f).ι ≫ pullback.snd f f

end GlobalTheory.EtC.Tr
