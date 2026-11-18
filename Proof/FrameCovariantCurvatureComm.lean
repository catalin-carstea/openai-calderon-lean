import Proof.ThreeConnectionCurvature
import Proof.FrameThreeConnection
import Proof.FrameCurvatureCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual first-order curvature action on angular functions, with
its genuine order-one Sobolev domain and codomain. -/
def frameCurvatureSobolevL (s : ℝ) (g : MetricField) (e : Frame) (y a b : X) :
    SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  -threeRotationL s (threeSkewCoordinates (frameCurvatureCoefficient g e y a b))

def frameCurvatureRotationL (g : MetricField) (e : Frame) (y a b : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  frameCurvatureSobolevL 1 g e y a b

theorem Elliptic.frameConnectionThreeLinear_curvature {Y : Set X} (hY : IsOpen Y)
    {K : ℝ} {g : MetricField} (hg : Elliptic Y K g) (hK : 0 < K)
    (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j)=if i=j then 1 else 0)
    {y : X} (hy : y ∈ Y) (a b : X) :
    threeConnectionCurvature (frameConnectionThreeLinear g e) y a b=
      threeSkewCoordinates (frameCurvatureCoefficient g e y a b) := by
  have hC := ((hg.contDiffOn_frameConnectionThreeLinear hY hK e he).contDiffAt
    (hY.mem_nhds hy)).differentiableAt (by simp)
  have hEq : threeVectorConnection (frameConnectionThreeLinear g e) =ᶠ[nhds y]
      frameConnectionOperator g e := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact (frameConnectionOperator_eq_threeLinear g e x
      (fun v => frameConnection_skew hY hg hK e he hFrame hx v)).symm
  have hCurv : curvatureLinear (threeVectorConnection (frameConnectionThreeLinear g e)) y a b=
      curvatureLinear (frameConnectionOperator g e) y a b := by
    simp only [curvatureLinear,hEq.fderiv_eq,hEq.eq_of_nhds]
  have hVec : threeRotationVectorL (threeConnectionCurvature (frameConnectionThreeLinear g e) y a b)=
      curvatureLinear (frameConnectionOperator g e) y a b :=
    (threeVectorConnection_curvature _ y a b hC).symm.trans hCurv
  have hCoords := congrArg (fun T : X →L[ℝ] X => threeSkewCoordinates (fun i j => T (axis i) j)) hVec
  rw [threeRotationVectorL_coordinates] at hCoords
  apply hCoords.trans
  congr 1
  funext i j
  exact hg.frameConnectionOperator_curvature_coordinate hY hK e he hFrame hy a b i j

/-- Exact curvature commutator of the actual fixed-physical-direction
covariant derivatives. All frame regularity assumptions are qualitative. -/
theorem Elliptic.highSectionCovariantDerivative_commutator {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    (U : X → SphereSobolev 2) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) (a b : X) :
    oneSectionCovariantDerivative d (fun x => highSectionCovariantDerivative d U x b) y a-
      oneSectionCovariantDerivative d (fun x => highSectionCovariantDerivative d U x a) y b=
    frameCurvatureRotationL d.γ d.frame y a b
      (sphereSobolevInclusionL 2 1 (by norm_num) (U y)) := by
  let C := frameConnectionThreeLinear d.γ d.frame
  let A := fun x v => threeRotationL 1 (C x v)
  let B := fun x v => threeRotationL 2 (C x v)
  have hSkew (x : X) (hx : x ∈ Y) (v : X) :=
    frameConnection_skew hY hg hK d.frame he hFrame hx v
  have hInner (v : X) : (fun x => highSectionCovariantDerivative d U x v) =ᶠ[nhds y]
      (fun x => gradedSectionCovariantDerivative (sphereSobolevInclusionL 2 1 (by norm_num)) B U x v) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact highSectionCovariantDerivative_eq_three d U x v (hSkew x hx v)
  have hOuter (V : X → SphereSobolev 1) (v : X) :
      oneSectionCovariantDerivative d V y v=
        gradedSectionCovariantDerivative (sphereSobolevInclusionL 1 0 (by norm_num)) A V y v :=
    oneSectionCovariantDerivative_eq_three d V y v (hSkew y hy v)
  rw [oneSectionCovariantDerivative_congr_germ (hInner b),
    oneSectionCovariantDerivative_congr_germ (hInner a),hOuter,hOuter]
  have hCD := ((hg.contDiffOn_frameConnectionThreeLinear hY hK d.frame he).contDiffAt
    (hY.mem_nhds hy)).differentiableAt (by simp)
  have hh := threeRotationSection_covariant_commutator C U y a b hCD (hU.contDiffAt (hY.mem_nhds hy))
  change _= -threeRotationL 1 (threeSkewCoordinates (frameCurvatureCoefficient d.γ d.frame y a b))
    (sphereSobolevInclusionL 2 1 (by norm_num) (U y))
  rw [hh,hg.frameConnectionThreeLinear_curvature hY hK d.frame he hFrame hy a b]

/-- The curvature remainder has a common first-order angular norm bound
from the frozen reference budgets through order two. -/
theorem Background.norm_frameCurvatureSobolevL_le (s : ℝ) {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    {y : X} (hy : y ∈ Ω) (a b : X) :
    ‖frameCurvatureSobolevL s g e y a b‖ ≤
      3*Real.sqrt 2*curvatureBudget K |M 0| |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| * ‖a‖*‖b‖ := by
  let CB := curvatureBudget K |M 0| |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
  have hCB : 0 ≤ CB := curvatureBudget_nonneg K _ _ _ (by linarith) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
  have hEntry (i j : I) : |frameCurvatureCoefficient g e y a b i j| ≤ CB*‖a‖*‖b‖ := by
    rw [← h.1.frameConnectionOperator_curvature_coordinate hΩ (by linarith) e
      h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2 hy a b i j]
    exact h.frameConnectionOperator_curvature_coordinate_bound hΩ hK hm hy a b i j
  have hP (i : I) : |threeSkewCoordinates (frameCurvatureCoefficient g e y a b) i| ≤ CB*‖a‖*‖b‖ := by
    fin_cases i
    · simpa [threeSkewCoordinates] using hEntry 0 1
    · simpa [threeSkewCoordinates] using hEntry 0 2
    · simpa [threeSkewCoordinates] using hEntry 1 2
  unfold frameCurvatureSobolevL
  rw [norm_neg]
  exact (norm_threeRotationL_le s _ (CB*‖a‖*‖b‖) (by positivity) hP).trans_eq (by ring)

theorem Background.norm_frameCurvatureRotationL_le {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    {y : X} (hy : y ∈ Ω) (a b : X) :
    ‖frameCurvatureRotationL g e y a b‖ ≤
      3*Real.sqrt 2*curvatureBudget K |M 0| |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| * ‖a‖*‖b‖ :=
  h.norm_frameCurvatureSobolevL_le 1 hΩ hK hm hy a b

lemma frameCurvatureSobolevL_inclusion (s t : ℝ) (hst : t ≤ s)
    (g : MetricField) (e : Frame) (y a b : X) :
    (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (frameCurvatureSobolevL s g e y a b)=
      (frameCurvatureSobolevL t g e y a b).comp (sphereSobolevInclusionL s t hst) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [frameCurvatureSobolevL,threeRotationL,ContinuousLinearMap.comp_apply,
    _root_.neg_apply,_root_.add_apply,_root_.smul_apply,map_neg,map_add,map_smul,
    sphereSobolevRotationL_inclusion_apply]

end ShrinkingSpheres
