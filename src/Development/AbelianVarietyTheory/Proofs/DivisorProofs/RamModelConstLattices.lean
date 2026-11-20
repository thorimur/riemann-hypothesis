import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamModelOfHypotheses

set_option autoImplicit false

open GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published

namespace GlobalTheory.EigWhole

theorem ramModel_constLattices : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd →
    RamModel :=
  ramModel_of_hypotheses

end GlobalTheory.EigWhole
