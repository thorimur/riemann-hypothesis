import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Radical.NatInt
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

namespace KStar.Ram

open NumberField
open scoped Pointwise

noncomputable def vdField (E : Type*) [Field E] [NumberField E] (p : ℕ) : ℚ :=
  (padicValInt p (discr E) : ℚ) / (Module.finrank ℚ E : ℚ)

noncomputable def vdAt {E : Type*} [Field E] [NumberField E] (P : Ideal (𝓞 E)) : ℚ :=
  (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (P.ramificationIdx ℤ : ℚ)

def SplitsIn (p : ℕ) (K : Type*) [Field K] [NumberField K] : Prop :=
  ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K

noncomputable def conjIdeal {E : Type*} [Field E] [NumberField E] [IsCMField E]
    (I : Ideal (𝓞 E)) : Ideal (𝓞 E) :=
  I.map (IsCMField.ringOfIntegersComplexConj E)

end KStar.Ram
