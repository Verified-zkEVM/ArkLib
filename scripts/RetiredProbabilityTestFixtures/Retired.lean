import Mathlib.Probability.Distributions.Uniform

namespace RetiredProbabilityTestFixtures.Retired

noncomputable def oldDistribution : PMF Bool := PMF.uniformOfFintype Bool

theorem retiredInType (p : PMF Bool) : p = p := rfl

noncomputable def retiredOnlyInBody : Bool := by
  classical
  exact decide ((PMF.pure true) true = 1)

private noncomputable def privateOldDistribution : PMF Bool := PMF.pure true

noncomputable def privateConsumer := privateOldDistribution

end RetiredProbabilityTestFixtures.Retired
