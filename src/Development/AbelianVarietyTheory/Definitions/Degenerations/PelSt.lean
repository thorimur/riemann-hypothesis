import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN

def PelSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
  [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (D : DegData R I) (A : PolAV (Sp (FractionRing R)))
  (U : Unif I D A t.G), U.LG = t.PP → ∃ P : PELUnif I t, P.D = D ∧ P.A = A ∧ HEq P.U U ∧ P.TorsionIso
end GlobalTheory.LN
end
