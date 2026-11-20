import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPowerSeries.Basic
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

namespace PI.WwEval

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def Gxz (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen c) (I s c)

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((MvPolynomial.coeff μ P : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def WwEval : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (x : Lt × ℕ × Fin N0 → ℂ_[l])
    (I : KM.ColChoice N1 nu),
    MvPolynomial.eval x (KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I)) =
      (let P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l] :=
        MvPolynomial.aeval (fun v : Lt × ℕ × Fin N1 => ∑ a : Fin N0,
          MvPolynomial.C (x (v.1, v.2.1, a)) * MvPolynomial.X ((v.1, a, v.2.2) : Lt × Fin N0 × Fin N1))
          (KM.nablaX N1 nu I)
       ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th)

end PI.WwEval
