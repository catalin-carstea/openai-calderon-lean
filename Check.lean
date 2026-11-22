import Consumer
import Applications.Local

-- Theorem 1.1
#check CalderonPatch.smoothAnisotropicUniqueness
#print axioms CalderonPatch.smoothAnisotropicUniqueness

-- Theorem 3.1
#check CalderonN.localMetricExtension
#print axioms CalderonN.localMetricExtension

-- Proposition 5.3
#check CalderonN.coercivity
#print axioms CalderonN.coercivity

-- Theorem 1.1 consumer
#check CalderonPatch.measuredGaugePreservesTangentEnergy
#print axioms CalderonPatch.measuredGaugePreservesTangentEnergy

-- Ambient-kernel consumer
#check CalderonN.localMetricExtensionFromDirichletKernels
#print axioms CalderonN.localMetricExtensionFromDirichletKernels

-- Chart gluing consumer
#check CalderonN.eventuallyEqMetric
#print axioms CalderonN.eventuallyEqMetric

-- Coercivity consumer
#check CalderonN.zeroEnergyOfZeroOutput
#print axioms CalderonN.zeroEnergyOfZeroOutput
