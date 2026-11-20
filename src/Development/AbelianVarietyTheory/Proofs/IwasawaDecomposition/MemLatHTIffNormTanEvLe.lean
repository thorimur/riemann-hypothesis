import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsGrpPullbackAbVarModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

variable {p : ℕ} [Fact p.Prime] {C : SCF p} {z : Sp ↥(intO ↥C.S) ⟶ X}

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {P : GlobalTheory.HTLat.Point p (fldVal C) ↥(intO ↥C.S) Λ}

def ev (x : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt) : P.OmC →ₗ[↥C.S] ↥C.S :=
  (Algebra.linearMap ↥(intO ↥C.S) ↥C.S ∘ₗ LinearMap.proj x ∘ₗ (ReciprocityTheory.ChartRestriction.G.Pdiv.omega P.Gt).subtype).liftBaseChange ↥C.S

variable {φ : P.G.left ⟶ t.G.left} (hφ : IsGrpPullback P.G t.G z φ)

end GlobalTheory.HTDual
