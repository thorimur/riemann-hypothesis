import Mathlib.Algebra.AffineMonoid.Basic
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

namespace PI.LocFramePrim

open NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

def ratTup {M n : ℕ} (X : Fin n → Fin M → E) : Fin n → Fin M → R ⊗[F] E :=
  fun a i => inclR R (X a i)

def ratV {n : ℕ} (x : Fin n → E) : Fin n → R ⊗[F] E := fun i => inclR R (x i)

end Alg

abbrev Fv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def latLoc (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) :
    Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' Λ)

end Level

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev TupV (n a : ℕ) : Type := Fin a → Fin n → Fv F v ⊗[F] E

def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))

def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)

variable {n : ℕ} (Λ : Set (Fin n → E))

def IsPrim {a : ℕ} (X : TupV (E := E) v n a) : Prop :=
  (∀ i, X i ∈ latLoc (E := E) v Λ) ∧
  ∀ c : Fin a → Fv F v ⊗[F] E, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ → ∀ i, c i ∈ OEv (E := E) v

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1

def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1

def locF {r : ℕ} (X : TupV (E := E) v n (r + 1)) : TupV (E := E) v n (r + 1) :=
  fun a => sc (E := E) v (alp v r a) • X a

end Frames

section Split

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ddE : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
  ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 E)) E)

variable {F}

def latSpan {n r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (w : Fin r → Fin n → E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ aa a ∧ y = x • w a}

end Split

def Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (n r : ℕ) (Λ Lb : Submodule (𝓞 E) (Fin n → E))
    (e f : Fin r → Fin n → E) (z : Fin n → E),
    Λ.FG →
    Λ = latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ⊔ Lb ⊔
      latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f →
    LinearIndependent E (Fin.append e f) →
    (∀ y ∈ Lb, y ∈ Submodule.span E (Set.range e ∪ Set.range f) → y = 0) →
    z ∈ Lb →
    (∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) →
    IsPrim v (Λ : Set (Fin n → E))
      (locF v (ratTup (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E)))

end PI.LocFramePrim
