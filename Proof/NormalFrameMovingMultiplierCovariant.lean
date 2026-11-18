import Proof.NormalFrameMovingMultiplierDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.NativeCoefficientBoundaryMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Finite covariant subtraction commutes with a fixed bounded linear map. -/
lemma linear_map_covariant_sum_identity
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : E →L[ℝ] F) (A : F) (B : ι → κ → F) (u : E) (v : ι → κ → E) (w : ι → κ → ℝ) :
    (A+L u)-(∑ i,∑ j,w i j • (B i j+L (v i j))) =
      (A-∑ i,∑ j,w i j • B i j)+L (u-∑ i,∑ j,w i j • v i j) := by
  simp only [map_sub,map_sum,map_smul,smul_add,Finset.sum_add_distrib]
  abel

lemma covariant_sum_identity_of_linear_point
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : E →L[ℝ] F) (G : E → F) (hG : ∀ u,G u = L u)
    (A : F) (Ar : ι → κ → F) (B : F) (Br : ι → κ → F)
    (u : E) (ur : ι → κ → E) (w : ι → κ → ℝ)
    (hA : A = B+G u) (hR : ∀ i j,Ar i j = Br i j+G (ur i j)) :
    (A-∑ i,∑ j,w i j • Ar i j) =
      (B-∑ i,∑ j,w i j • Br i j)+G (u-∑ i,∑ j,w i j • ur i j) := by
  rw [hA]
  simp_rw [hR,hG]
  exact linear_map_covariant_sum_identity L B Br u ur w

attribute [local irreducible] NormalFrameMultiplierGainFamily.gain NormalFrameMultiplierGainFamily.gainInMultiplier
  radialTaylorMultiplierInMultiplierL radialTaylorMultiplierCommutatorL nativeBulkMultiplierForcingInMultiplierL

/-- The actual covariant derivative of a moving-multiplier gain splits
exactly into the fixed-multiplier covariant derivative and the SAME point
gain applied to the covariant multiplier derivative. -/
theorem NormalFrameMultiplierGainFamily.covariant_moving_multiplier_identity
    {d : Data} {y : X} {A : NormalFrameParameter × X → Mat} {hA : ContDiff ℝ ∞ A}
    {S : Set X} {hS : IsCompact S} {hz : ∀ p z,z ∉ S → A (p,z) = 0}
    {F0 : SmoothCoefficientMatrix 2}
    {ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)} {V : Set NormalFrameParameter}
    (T : NormalFrameMultiplierGainFamily d A hA S hS hz F0 ha0 (d.radius y) V
      (y,(d.radius y,frameVectorLinear d.frame y)))
    (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
      (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
    (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p)))
    (hr : DifferentiableAt ℝ d.radius y) (he : DifferentiableAt ℝ (frameVectorLinear d.frame) y)
    (q : NormalFrameParameter → SmoothCoefficientJets 3)
    (hq : DifferentiableAt ℝ q (y,(d.radius y,frameVectorLinear d.frame y))) (a : X) :
    let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
    let ca := normalFrameActualCurve d.frame d.radius y a
    let cr := fun i j => normalFrameRotationCurve d.frame d.radius y i j
    let w := fun i j => (1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j
    (deriv (fun t => T.gain (q (ca t)) (ca t)) 0-
      ∑ i,∑ j,w i j • deriv (fun t => T.gain (q (cr i j t)) (cr i j t)) 0) =
    (deriv (fun t => T.gain (q p0) (ca t)) 0-
      ∑ i,∑ j,w i j • deriv (fun t => T.gain (q p0) (cr i j t)) 0)+
    T.gain (deriv (fun t => q (ca t)) 0-
      ∑ i,∑ j,w i j • deriv (fun t => q (cr i j t)) 0) p0 := by
  dsimp only
  have hActual := T.deriv_gain_moving_multiplier_curve hStrong hCoercive
    (normalFrameActualCurve d.frame d.radius y a) _
    (hasDerivAt_normalFrameActualCurve d.frame d.radius y a hr he)
    (normalFrameActualCurve_zero d.frame d.radius y a) q hq
  have hRot (i j : I) := T.deriv_gain_moving_multiplier_curve hStrong hCoercive
    (normalFrameRotationCurve d.frame d.radius y i j) _
    (hasDerivAt_normalFrameRotationCurve d.frame d.radius y i j)
    (normalFrameRotationCurve_zero d.frame d.radius y i j) q hq
  exact covariant_sum_identity_of_linear_point
    (T.gainInMultiplier (y,(d.radius y,frameVectorLinear d.frame y)))
    (fun Q => T.gain Q (y,(d.radius y,frameVectorLinear d.frame y)))
    (fun Q => (T.gainInMultiplier_apply _ Q).symm) _ _ _ _ _ _ _ hActual hRot

end ShrinkingSpheres
