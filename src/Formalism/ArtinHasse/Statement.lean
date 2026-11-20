import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Exp
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

open PowerSeries

namespace Formalism.FT

def tSeries : PowerSeries (MvPolynomial ℕ ℚ) :=
  PowerSeries.mk fun m => if m = 0 then 0 else MvPolynomial.X m

def Hpoly (k : ℕ) : MvPolynomial ℕ ℚ :=
  coeff k ((PowerSeries.exp (MvPolynomial ℕ ℚ)).subst tSeries)

def HDeriv : Prop :=
  ∀ r k : ℕ, 1 ≤ r →
    MvPolynomial.pderiv r (Hpoly k) = if r ≤ k then Hpoly (k - r) else 0

def HAtPsum : Prop :=
  ∀ (n k : ℕ),
    MvPolynomial.aeval (fun m : ℕ => (m : ℚ)⁻¹ • MvPolynomial.psum (Fin n) ℚ m) (Hpoly k) =
      MvPolynomial.hsymm (Fin n) ℚ k

abbrev hPS (R : Type*) [CommRing R] (n k : ℕ) : MvPowerSeries (Fin n) R :=
  ((MvPolynomial.hsymm (Fin n) R k : MvPolynomial (Fin n) R) : MvPowerSeries (Fin n) R)

def SymmSeriesHsymm : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (F : MvPowerSeries (Fin n) R),
    (∀ π : Equiv.Perm (Fin n),
      F.subst (fun i => (MvPowerSeries.X (π i) : MvPowerSeries (Fin n) R)) = F) →
    ∃! G : MvPowerSeries (Fin n) R, G.subst (fun j : Fin n => hPS R n (j.val + 1)) = F

def HsymmStable : Prop :=
  ∀ (R : Type) [CommRing R] (n k : ℕ),
    MvPolynomial.aeval
        (fun i : Fin (n + 1) => if h : i.val < n then (MvPolynomial.X ⟨i.val, h⟩ : MvPolynomial (Fin n) R) else 0)
        (MvPolynomial.hsymm (Fin (n + 1)) R k) =
      MvPolynomial.hsymm (Fin n) R k

def ltLogQ (p : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => by
    classical exact if ∃ j : ℕ, p ^ j = n then ((n : ℚ))⁻¹ else 0

def artinHasse (p : ℕ) : PowerSeries ℚ := (PowerSeries.exp ℚ).subst (ltLogQ p)

def DworkLemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : PowerSeries ℚ_[p]), constantCoeff f = 1 →
    ((∀ n, ‖coeff n f‖ ≤ 1) ↔
      ∃ g : PowerSeries ℚ_[p], (∀ n, ‖coeff n g‖ ≤ 1) ∧
        f.subst ((PowerSeries.X : PowerSeries ℚ_[p]) ^ p) =
          f ^ p * (1 + (p : ℚ_[p]) • (PowerSeries.X * g)))

def ArtinHasseIntegral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), ¬ p ∣ (coeff n (artinHasse p)).den

def carries (p : ℕ) [Fact p.Prime] (y : ℤ_[p]) (i : ℕ) : Set ℕ :=
  {e : ℕ | 1 ≤ e ∧ p ^ e ≤ i % p ^ e + y.appr e}

def KummerZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (y : ℤ_[p]) (i : ℕ), Ring.choose (y + i) i ≠ 0 →
    (carries p y i).Finite ∧
      ‖Ring.choose (y + i) i‖ = (p : ℝ) ^ (-((carries p y i).ncard : ℤ))

end Formalism.FT
