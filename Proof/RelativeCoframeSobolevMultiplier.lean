import Proof.NormalFrameRelativeCoframeGeometry
import Proof.UniformNormalFrameRelativeCoframeJets
import Proof.CoordinateMultiplierSobolev
import Proof.ClosedBoundaryGradientAdjoint
import Proof.PhysicalFixedCenterGradient
import Proof.SmoothFiniteJetBounds
import Proof.FiniteJetLinearCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 1800
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def relativeCoframeNormalSobolevL (s : ℝ) (g : MetricField) (a : X) (p : NormalFrameRelativeParameter) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  ∑ j : I,normalFrameRelativeCoframeValue g a j p • coordinateMultiplierSobolevL s j

def coframeNormalSobolevBudget (s : ℝ) : ℝ := ∑ j : I,‖coordinateMultiplierSobolevL s j‖

lemma coframeNormalSobolevBudget_nonneg (s : ℝ) : 0 ≤ coframeNormalSobolevBudget s := by
  unfold coframeNormalSobolevBudget
  positivity

lemma relativeCoframeNormalSobolev_inclusion (s t : ℝ) (hst : t ≤ s)
    (g : MetricField) (a : X) (p : NormalFrameRelativeParameter) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (relativeCoframeNormalSobolevL s g a p u) =
      relativeCoframeNormalSobolevL t g a p (sphereSobolevInclusionL s t hst u) := by
  simp only [relativeCoframeNormalSobolevL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun z : SphereSobolev t => normalFrameRelativeCoframeValue g a j p • z)
  exact sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics s t hst (axis j) u

lemma relativeCoframeNormalSobolev_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (s : ℝ) (q : I → P → ℝ) (p : P) (N : ℕ) (B : ℝ)
    (hq : ∀ j,SmoothFiniteJetBound (q j) p N B) :
    SmoothFiniteJetBound (fun x => ∑ j : I,q j x • coordinateMultiplierSobolevL s j) p N
      (coframeNormalSobolevBudget s*B) := by
  exact SmoothFiniteJetBound.linearCombination q (coordinateMultiplierSobolevL s) p N B hq

lemma relativeCoframeNormalSobolev_point {Ω : Set X}
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {d : Data}
    (h : Background Ω K M d.γ d.g₁ d.g₂ d.frame) {y : X} (hy : y ∈ Ω)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (a : X) :
    relativeCoframeNormalSobolevL 1 d.γ a ((y,frameVectorLinear d.frame y),0) =
      oneBoundaryCoefficientMulL (vectorNormalJet (fixedCenterCoefficient Q d.γ d.frame y a)) := by
  have he (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j)) = if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using h.2.2.2.2.2.2.2 y hy i j
  have hCoeff (j : I) : oneBoundaryCoefficientMulL (fixedCenterCoefficient Q d.γ d.frame y a j) =
      (frameCoordinateLinear d.γ d.frame y j a) • ContinuousLinearMap.id ℝ (SphereSobolev 1) := by
    apply oneBoundaryCoefficientMulL_const_sphere
    intro w
    have hw : w.val ∈ Metric.closedBall (0:X) 1 := Metric.sphere_subset_closedBall w.property
    change coefficientValue 2 (constantBoundaryCoefficient Q (frameCoordinateLinear d.γ d.frame y j a)) w.val = _
    rw [constantBoundaryCoefficient,coefficientValue_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [(hQ w.val hw).eq_of_nhds,mul_one]
  rw [oneBoundary_vectorNormal_decomposition]
  apply ContinuousLinearMap.ext
  intro u
  simp only [relativeCoframeNormalSobolevL,_root_.sum_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,hCoeff,ContinuousLinearMap.id_apply,map_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [normalFrameRelativeCoframeValue_orthonormal _ _ _ _ _ he]
  simp only [frameCoordinateLinear_apply,frameVectorLinear_apply,frameVector_axis]
  rfl

theorem uniform_relative_coframe_normal_three_jets {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) (s : ℝ) :
    ∃ CM : ℝ,0 ≤ CM ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),Background Ω K M g g₁ g₂ e →
      ∀ y ∈ Ω,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) → ∀ a : X,
      SmoothFiniteJetBound (relativeCoframeNormalSobolevL s g a) ((y,L),0) 3 (CM*‖a‖) := by
  obtain ⟨C,hC,hData⟩ := uniform_normalFrameRelativeCoframe_higher_jets hΩ 3 hm K M hK
  have hC0 := zero_le_one.trans hC
  have hM := coframeNormalSobolevBudget_nonneg s
  refine ⟨coframeNormalSobolevBudget s*C,mul_nonneg hM hC0,?_⟩
  intro g g₁ g₂ e hd y hy L he a
  have hh := relativeCoframeNormalSobolev_jet_bound s (fun j => normalFrameRelativeCoframeValue g a j)
    ((y,L),0) 3 (C*‖a‖) (fun j =>
      ⟨by positivity,(hData g g₁ g₂ e hd y hy L he a j).1,(hData g g₁ g₂ e hd y hy L he a j).2⟩)
  change SmoothFiniteJetBound (fun x => ∑ j : I,normalFrameRelativeCoframeValue g a j x • coordinateMultiplierSobolevL s j)
    ((y,L),0) 3 ((coframeNormalSobolevBudget s*C)*‖a‖)
  simpa only [mul_assoc] using hh
end ShrinkingSpheres
