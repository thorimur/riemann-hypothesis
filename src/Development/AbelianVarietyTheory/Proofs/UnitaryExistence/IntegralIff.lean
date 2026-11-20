import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.IntegralData

theorem integralIff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntegralIffSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y
  constructor
  · rintro ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩
    exact ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩
  · rintro ⟨⟨G, t', m1, m2, ub, h1, h2, h3, h4, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩⟩
    exact ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, θ, h5, w1, w2, σ, s1, θ2, r1, r2, a1, a2, p, g⟩

end GlobalTheory.IntegralData
