import Proof.ParallelFirstSelfBalancedWeakCurvature
import Proof.HalfScalarTransposeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact local Hodge exchange in balanced half endpoints. Every selected
higher source is used only through its genuine inclusion square. -/
theorem balanced_half_hodge_pair_identity {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ k,ContDiffOn ℝ ∞ (fun x => d.frame x k) Y)
    (hFrame : ∀ x ∈ Y,∀ k l,metricPair d.γ x (d.frame x k) (d.frame x l)=if k=l then 1 else 0)
    (q : X → ℝ) (LR LS : X → SphereSobolev (1/2:ℝ))
    (HR HS : X → SphereSobolev (3/2:ℝ)) (hLS : ContDiffOn ℝ ∞ LS Y)
    (hHS : ∀ x ∈ Y,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (HS x)=LS x)
    {y : X} (hy : y ∈ Y) (a b : X) :
    let R := fun v x => balancedPositiveHalfDerivative d LR HR x v
    let G := fun v x => balancedPositiveHalfDerivative d LS HS x v
    let V := fun v x => weakHalfSourceCovariantDerivative d LS x v
    let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    q y*(⟪Z (R b y),Z (G a y)⟫_ℝ-⟪Z (R a y),Z (G b y)⟫_ℝ)=
      q y*sphereSobolevDualPairing (1/2:ℝ) (LR y)
        (frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y a b (LS y))+
      fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ) (LR y) (V b y)-
      fderiv ℝ q y b*sphereSobolevDualPairing (1/2:ℝ) (LR y) (V a y)+
      balancedSourceHalfPairDensity d q LR HR (V a) (G a) b y-
      balancedSourceHalfPairDensity d q LR HR (V b) (G b) a y := by
  dsimp only
  let G := fun v x => balancedPositiveHalfDerivative d LS HS x v
  let V := fun v x => weakHalfSourceCovariantDerivative d LS x v
  have hG (v x : X) (hx : x ∈ Y) : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (G v x)=V v x :=
    balanced_positive_half_derivative_weak_graph d LS HS x v (hHS x hx)
  have hComm := balanced_weak_half_source_commutator hY d hg hK he hFrame LS hLS G hG hy a b
  have hPa : sphereSobolevDualPairing (1/2:ℝ) (balancedPositiveHalfDerivative d LR HR y b) (V a y)=
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (balancedPositiveHalfDerivative d LR HR y b),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (G a y)⟫_ℝ := by
    rw [←hG a y hy,half_dual_pairing_inclusion]
  have hPb : sphereSobolevDualPairing (1/2:ℝ) (balancedPositiveHalfDerivative d LR HR y a) (V b y)=
      ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (balancedPositiveHalfDerivative d LR HR y a),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (G b y)⟫_ℝ := by
    rw [←hG b y hy,half_dual_pairing_inclusion]
  change _=q y*sphereSobolevDualPairing (1/2:ℝ) (LR y)
      (frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y a b (LS y))+
    fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ) (LR y) (V b y)-
    fderiv ℝ q y b*sphereSobolevDualPairing (1/2:ℝ) (LR y) (V a y)+
    balancedSourceHalfPairDensity d q LR HR (V a) (G a) b y-
    balancedSourceHalfPairDensity d q LR HR (V b) (G b) a y
  rw [←hComm]
  unfold balancedSourceHalfPairDensity
  rw [hPa,hPb]
  simp only [sphereSobolevDualPairing,inner_sub_right]
  ring

end ShrinkingSpheres.ParallelEnergy
