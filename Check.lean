module

import Applications.Manuscript.Corollary12
import Applications.Manuscript.Corollary13
import Applications.Manuscript.Lemma21
import Applications.Manuscript.Proposition22
import Applications.Manuscript.Lemma23
import Applications.Manuscript.Lemma32
import Applications.Manuscript.Proposition33
import Applications.Manuscript.Lemma34
import Applications.Manuscript.Proposition35
import Applications.Manuscript.Lemma41
import Applications.Manuscript.Proposition42
import Applications.Manuscript.Proposition43
import Applications.Manuscript.Lemma51
import Applications.Manuscript.Lemma52
import Applications.Manuscript.Lemma54
import Applications.Manuscript.Lemma61
import Applications.Manuscript.Lemma62
import Applications.Manuscript.Lemma63
import Applications.Manuscript.Proposition71
import Applications.Manuscript.Proposition72
import Applications.Manuscript.Lemma81
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

-- Standalone manuscript claims
#print axioms CalderonPaper.corollary12
#print axioms CalderonPaper.corollary13
#print axioms CalderonPaper.lemma21
#print axioms CalderonPaper.proposition22
#print axioms CalderonPaper.lemma23
#print axioms CalderonPaper.lemma32
#print axioms CalderonPaper.proposition33
#print axioms CalderonPaper.lemma34
#print axioms CalderonPaper.proposition35
#print axioms CalderonPaper.lemma41
#print axioms CalderonPaper.proposition42
#print axioms CalderonPaper.proposition43
#print axioms CalderonPaper.lemma51
#print axioms CalderonPaper.lemma52
#print axioms CalderonPaper.lemma54
#print axioms CalderonPaper.lemma61
#print axioms CalderonPaper.lemma62
#print axioms CalderonPaper.lemma63
#print axioms CalderonPaper.proposition71
#print axioms CalderonPaper.proposition72
#print axioms CalderonPaper.lemma81

-- Corollary consumers
#print axioms CalderonPaper.fullBoundaryFixesSpecifiedPoint
#print axioms CalderonPaper.scalarConductivitiesAgreeAtBoundary
