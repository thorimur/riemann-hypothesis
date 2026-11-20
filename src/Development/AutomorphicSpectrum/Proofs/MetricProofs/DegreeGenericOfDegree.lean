import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreDegreeSum

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem degreeGeneric_of_degree :
    ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement → GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement := by
  intro hDeg K _ _ ι _ P e L hP hL
  classical
  rw [hDeg K ι P e L 2 hP hL Nat.prime_two,
    GroundTheory.Heights₂.Heights.Targets.FibreDegreeSum.proof K ι P e (fun j => (L j).a) 2 hP Nat.prime_two,
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P _)]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.Ar.Giv
