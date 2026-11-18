import Proof.NativeHalfMultiplierTaylorScaledDerivative
import Proof.MultiplierFirstVariationKernel
import Proof.CoefficientOperatorLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeWeakHalfLift nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse functionalInverse nativeZeroFunctionalInverse

lemma nativeBulkMultiplierForcing_congr_unitBall (F G : SmoothCoefficientMatrix 2)
    (Q : SmoothCoefficientJets 3)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = coefficientMatrixField 2 G z) :
    nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F (fun _ => 0) Q =
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus G (fun _ => 0) Q := by
  have h := nativeBulkMultiplierForcing_affine_on_ball fixedSobolevCalculus F G 0 Q 0 (by
    intro z hz i j
    have hEntry := congrArg (fun M : Mat => M i j) (hField z hz)
    change coefficientValue 2 (F i j) z = coefficientValue 2 (G i j) z at hEntry
    simpa only [zero_mul,add_zero] using hEntry)
  simpa only [zero_smul,add_zero] using h

lemma weakFirstPoissonVariation_congr_unitBall (c : ℝ) {a b : X → Mat}
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb : MemLp (fun z => TauCeti.PDE.energyIntegrand (b z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hField : ∀ z ∈ (ballOpens:Set X),a z = b z) :
    weakFirstPoissonVariationL c a ha = weakFirstPoissonVariationL c b hb := by
  have hE := (nativeWeakEnergy_congr_unitBall ha hb hField).2.1
  dsimp only [weakFirstPoissonVariationL]
  rw [hE]

lemma halfRadialMultiplierCommutator_congr_unitBall (F G : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 G z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = coefficientMatrixField 2 G z) :
    halfRadialMultiplierCommutatorL F ha Q = halfRadialMultiplierCommutatorL G hb Q := by
  have hS := strongDirichletOperator_congr_on_ball fixedSobolevCalculus 0 F G hField
  have hK := nativeBulkMultiplierForcing_congr_unitBall F G Q hField
  have hW := nativeWeakHalfLift_congr_unitBall ha hb hField
  rw [halfRadialMultiplierCommutator_trace_product,halfRadialMultiplierCommutator_trace_product,hS,hK,hW]

lemma halfMultiplierFirstVariation_congr_unitBall (F0 F1 G0 G1 : SmoothCoefficientMatrix 2)
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 G1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3)
    (hBase : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = coefficientMatrixField 2 G0 z)
    (hFirst : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F1 z = coefficientMatrixField 2 G1 z) :
    halfMultiplierFirstVariationL F0 F1 ha1 Q = halfMultiplierFirstVariationL G0 G1 hb1 Q := by
  have hS0 := strongDirichletOperator_congr_on_ball fixedSobolevCalculus 0 F0 G0 hBase
  have hS1 := strongDirichletOperator_congr_on_ball fixedSobolevCalculus 0 F1 G1 hFirst
  have hK0 := nativeBulkMultiplierForcing_congr_unitBall F0 G0 Q hBase
  have hK1 := nativeBulkMultiplierForcing_congr_unitBall F1 G1 Q hFirst
  have hP1 := weakFirstPoissonVariation_congr_unitBall 1
    (a:=coefficientMatrixField 2 F1) (b:=coefficientMatrixField 2 G1) ha1 hb1 hFirst
  have hI0 := congrArg (fun T : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => T.inverse) hS0
  exact (halfMultiplierFirstVariation_kernel F0 F1 ha1 Q).trans
    ((multiplierFirstVariationKernel_congr hI0 hS1 hK0 hK1 hP1).trans
      (halfMultiplierFirstVariation_kernel G0 G1 hb1 Q).symm)

/-- The entire gained Taylor operator depends only on the three coefficient
fields on the physical ball. In particular all flat cutoff choices are
exactly compatible, before any parameter differentiation. -/
theorem radialTaylorMultiplierCommutator_congr_unitBall (F F0 F1 G G0 G1 : SmoothCoefficientMatrix 2)
    (ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 G z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 G0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb1 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 G1 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) (r : ℝ)
    (hField : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = coefficientMatrixField 2 G z)
    (hBase : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = coefficientMatrixField 2 G0 z)
    (hFirst : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F1 z = coefficientMatrixField 2 G1 z) :
    radialTaylorMultiplierCommutatorL F F0 F1 ha ha0 ha1 Q r =
      radialTaylorMultiplierCommutatorL G G0 G1 hb hb0 hb1 Q r := by
  unfold radialTaylorMultiplierCommutatorL
  rw [halfRadialMultiplierCommutator_congr_unitBall F G ha hb Q hField,
    halfRadialMultiplierCommutator_congr_unitBall F0 G0 ha0 hb0 Q hBase,
    halfMultiplierFirstVariation_congr_unitBall F0 F1 G0 G1 ha1 hb1 Q hBase hFirst]

/-- Local agreement of the SAME three coefficient families gives equality
of their gained operator germs, even when the radius varies. This transfers
all existing parameter jets without a fresh PDE estimate. -/
theorem radialTaylorMultiplierCommutator_family_germ_congr
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F F1 G G1 : P → SmoothCoefficientMatrix 2) (F0 G0 : SmoothCoefficientMatrix 2)
    (ha : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F p) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha1 : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (F1 p) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (G p) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb1 : ∀ p,MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 (G1 p) z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (hb0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 G0 z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) (r : P → ℝ) (x : P)
    (hField : ∀ᶠ p in 𝓝 x,∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (F p) z = coefficientMatrixField 2 (G p) z)
    (hFirst : ∀ᶠ p in 𝓝 x,∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 (F1 p) z = coefficientMatrixField 2 (G1 p) z)
    (hBase : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = coefficientMatrixField 2 G0 z) :
    (fun p => radialTaylorMultiplierCommutatorL (F p) F0 (F1 p) (ha p) ha0 (ha1 p) Q (r p)) =ᶠ[𝓝 x]
      (fun p => radialTaylorMultiplierCommutatorL (G p) G0 (G1 p) (hb p) hb0 (hb1 p) Q (r p)) := by
  filter_upwards [hField,hFirst] with p hp hp1
  exact radialTaylorMultiplierCommutator_congr_unitBall (F p) F0 (F1 p) (G p) G0 (G1 p)
    (ha p) ha0 (ha1 p) (hb p) hb0 (hb1 p) Q (r p) hp hBase hp1

end ShrinkingSpheres
