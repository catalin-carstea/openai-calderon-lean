module

public import Proof.Manuscript.MovingTrace.CollarNormalizedSplit
public import Proof.Manuscript.MovingTrace.SmoothCollarLift
public import Proof.CalderonN.MetricBallDirichlet
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 3000000

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Matrix Metric
open scoped ContDiff

namespace CalderonPaper

variable {n : ℕ}
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

def complexNegativeBallDivergence (a : MetricField (n+1)) (v : Z → ℂ) (z : Z) : ℂ :=
  ⟨negativeBallDivergence a (Complex.reCLM ∘ v) z,
    negativeBallDivergence a (Complex.imCLM ∘ v) z⟩

/-- Lift the finite model to the ball without changing the differential
expression in the overlap. The factor on the split equation is the
physical metric volume times its inverse radial entry. -/
theorem complexNegativeBallDivergence_eq_collarSplit
    {U : Set Z} (hU : IsOpen U) {g a : MetricField (n+1)} (hg : SmoothMetric U g)
    (ha : ∀ z ∈ U, ∀ i j, a z i j = divergenceCoeff g z i j)
    (v : ↥S) {w : Z → ℂ} (hw : ContDiff ℝ ∞ w)
    {V : X n × ℝ → ℂ} (hV : ContDiff ℝ ∞ V)
    (he : EqOn (w ∘ polarCollar (angularPoint v)) V {q | q.2 < 1})
    (x : X n) (t : ℝ) (ht : t < 1) (hz : polarCollar (angularPoint v) (x,t) ∈ U)
    (hMixed : ∀ j : I n, pullbackMetric g (signedSphericalCollar v)
      (signedLayerCoordinates (x,t)) 0 j.succ = 0) :
    let m := pullbackMetric g (signedSphericalCollar v)
    let z := polarCollar (angularPoint v) (x,t)
    complexNegativeBallDivergence a w z =
      ((chartVolume g z * collarInverseRadial m (x,t) : ℝ) : ℂ) *
      complexSplitOperator (Matrix.of (fun i j => (collarTangential m (x,t) i j : ℂ)))
        (collarNormalDrift m (x,t) : ℂ) (fun i => (collarTangentDrift m (x,t) i : ℂ)) V x t := by
  dsimp only
  let F := signedSphericalCollar v
  let q := signedLayerCoordinates (x,t)
  let z := polarCollar (angularPoint v) (x,t)
  let m := pullbackMetric g F
  have hFq : F q = z := by
    change polarCollar (angularPoint v) (signedLayerCoordinates.symm (signedLayerCoordinates (x,t))) = z
    rw [signedLayerCoordinates.symm_apply_apply]
  have hDet : (coordinateJacobian F q).det ≠ 0 :=
    coordinateJacobian_det_ne_zero (signedSphericalCollar_derivative_bijective v q
      (by simpa only [q,signedLayerCoordinates.symm_apply_apply] using ht))
  let W := {q' : Z | (signedLayerCoordinates.symm q').2 < 1}
  have hW : IsOpen W := isOpen_lt (continuous_snd.comp signedLayerCoordinates.symm.continuous) continuous_const
  have hqW : q ∈ W := by simpa only [W,mem_ofPred_eq,q,signedLayerCoordinates.symm_apply_apply] using ht
  let T := W ∩ F ⁻¹' U
  have hT : IsOpen T := hW.inter (hU.preimage (signedSphericalCollar_contDiff v).continuous)
  have hqT : q ∈ T := ⟨hqW,by change F q ∈ U; rw [hFq]; exact hz⟩
  have hm : SmoothMetric T m :=
    smoothMetric_pullbackMetric hg (signedSphericalCollar_contDiff v) (fun _ hq => hq.2)
      (fun x hx => coordinateJacobian_det_ne_zero (signedSphericalCollar_derivative_bijective v x hx.1))
  have hqPos : (m q).PosDef := hm.2 q hqT
  let μ := collarInverseRadial m (x,t)
  have hμ : 0 < μ := inverseRadial_pos_of_posDef hqPos
  have hInv := inverseMixed_zero_of_metric_mixed_zero hqPos hMixed
  have hEqual (u : ℂ →L[ℝ] ℝ) :
      EqOn ((u ∘ w) ∘ F) (u ∘ V ∘ signedLayerCoordinates.symm) T := by
    intro y hy
    exact congrArg u (he hy.1)
  have hPull (u : ℂ →L[ℝ] ℝ) :
      laplace m (u ∘ V ∘ signedLayerCoordinates.symm) q = laplace g (u ∘ w) z := by
    rw [← laplace_congrOn (g := m) (h := m) hT (fun _ _ => rfl) (hEqual u) hqT,
      laplace_pullbackMetric (F := F) hU hg (signedSphericalCollar_contDiff v)
        (u.contDiff.comp hw).contDiffOn (show F q ∈ U from hqT.2) hDet,hFq]
  have hNeg (u : ℂ →L[ℝ] ℝ) :
      negativeBallDivergence a (u ∘ w) z = -(chartVolume g z * laplace g (u ∘ w) z) :=
    negativeBallDivergence_eq_neg_laplace hU hg ha (u.contDiff.comp hw).contDiffOn hz
  have hSplit := complexSplitOperator_eq_normalized_neg_laplace m hV x t hμ hInv
  dsimp only at hSplit
  change complexNegativeBallDivergence a w z =
    ((chartVolume g z * μ : ℝ) : ℂ) *
      complexSplitOperator (Matrix.of (fun i j => (collarTangential m (x,t) i j : ℂ)))
        (collarNormalDrift m (x,t) : ℂ) (fun i => (collarTangentDrift m (x,t) i : ℂ)) V x t
  unfold collarTangential collarNormalDrift collarTangentDrift collarInverseRadial
  rw [hSplit]
  change complexNegativeBallDivergence a w z = ((chartVolume g z * μ : ℝ) : ℂ) *
    ⟨-laplace m (Complex.reCLM ∘ V ∘ signedLayerCoordinates.symm) q / μ,
      -laplace m (Complex.imCLM ∘ V ∘ signedLayerCoordinates.symm) q / μ⟩
  rw [hPull Complex.reCLM, hPull Complex.imCLM]
  apply Complex.ext
  · simp only [complexNegativeBallDivergence,hNeg Complex.reCLM,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    field_simp [hμ.ne']
  · simp only [complexNegativeBallDivergence,hNeg Complex.imCLM,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero]
    field_simp [hμ.ne']

end CalderonPaper
