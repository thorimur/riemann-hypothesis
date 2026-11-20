import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Module.Lattice
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
import Mathlib.RingTheory.DedekindDomain.Different
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

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

def latSpanV {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {r : ℕ} (c : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (v : Fin r → V) :
    Submodule (𝓞 E) V :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ c a ∧ y = x • v a}

def SatBasisV : Prop :=
  ∀ (E V : Type) [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (Λ : Submodule (𝓞 E) V), Submodule.IsLattice E Λ →
    ∀ (n : ℕ) (w : Fin (n + 1) → V), LinearIndependent E w →
    ∀ a : Fin n → FractionalIdeal (nonZeroDivisors (𝓞 E)) E, (∀ i, a i ≠ 0) →
    ∃ (e : Fin (n + 1) → V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      LinearIndependent E e ∧ Submodule.span E (Set.range e) = Submodule.span E (Set.range w) ∧ c ≠ 0 ∧
      Λ ⊓ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E) =
        latSpanV (Fin.snoc (α := fun _ => FractionalIdeal (nonZeroDivisors (𝓞 E)) E) a c) e

def SplitDiff : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (p : ℕ) (P : Ideal (𝓞 E)),
    p.Prime → P.IsMaximal → ((p : ℕ) : 𝓞 E) ∈ P → ((p : ℕ) : 𝓞 E) ∉ P ^ 2 →
      ¬ (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) ≤ P)

end Formalism.L2.SG.Pf.LatEx
