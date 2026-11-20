import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayRos.Star

open Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RayHoriz ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {S : Type} [CommRing S] {ρ : Type} [Fintype ρ] [DecidableEq ρ]

def bilP (A : ρ → ρ → S) : MvPolynomial (Fin 2 × ρ) S :=
  ∑ r, ∑ s, MvPolynomial.C (A r s) * MvPolynomial.X ((0 : Fin 2), r) * MvPolynomial.X ((1 : Fin 2), s)

def sw (p : Fin 2 × ρ) : Fin 2 × ρ := (![1, 0] p.1, p.2)

end Alg

section Geo

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
  {ρ : Type} [Fintype ρ] [DecidableEq ρ] (L : LB G.left) {O : Type} [CommRing O]

end Geo

end GlobalTheory.RayRos.Star
