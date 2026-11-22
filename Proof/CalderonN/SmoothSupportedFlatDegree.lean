module

public import Proof.CalderonN.SmoothSupportedTraceFiberAction
public import Proof.CalderonN.SmoothTraceFlatDegree

public import Proof.CalderonN.ParametricBallConormal
public import Proof.CalderonN.FlatBallPolynomials
import Proof.CalderonN.MetricBallDirichlet
import Mathlib.Tactic

/-! Joint smoothness of the flat degree on sections, using the same
classical Dirichlet conormal that realizes it fiberwise. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem contDiffOn_parametricFlatBallConormal (G : X dim × X dim → ℝ)
    (hG : ContDiff ℝ ∞ G) :
    ContDiffOn ℝ ∞ (parametricBallConormal (fun _ => flatBallMetric 1 (0:X dim)) G)
      ((univ : Set (X dim)) ×ˢ ({0}ᶜ : Set (X dim))) := by
  intro q hq
  obtain ⟨V,hV,hqV,hCon⟩ := exists_contDiffOn_parametricBallConormal
    (U:=univ) (T:=univ) isOpen_univ isOpen_univ q.1 (subset_univ _) (subset_univ _)
    (g:=fun _ => flatBallMetric 1 (0:X dim)) (fun _ _ => contDiffOn_const)
    (fun _ _ => (smoothMetric_flatBallMetric (dim:=dim) one_pos).2 _ (mem_univ _)) hG.contDiffOn
  have hN : V ×ˢ ({0}ᶜ : Set (X dim)) ∈ nhds q :=
    (hV.prod isClosed_singleton.isOpen_compl).mem_nhds ⟨hqV,hq.2⟩
  exact (hCon.contDiffAt hN).contDiffWithinAt

variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

theorem smoothTraceFlatDegree_eq_parametricFlatBallConormal
    (G : X dim × X dim → ℝ) (hG : ContDiff ℝ ∞ G) (x : X dim) (z : ↥(standardSphere dim)) :
    (smoothTraceFlatDegree hA hEll S
      (smoothSphereTrace ⟨fun w => G (x,w),hG.comp (contDiff_const.prodMk contDiff_id)⟩)).1 z =
      parametricBallConormal (fun _ => flatBallMetric 1 (0:X dim)) G (x,z) := by
  let f : SmoothData dim := ⟨fun w => G (x,w),hG.comp (contDiff_const.prodMk contDiff_id)⟩
  let m := flatBallMetric (dim:=dim) 1
  have hm : SmoothMetric univ m := smoothMetric_flatBallMetric one_pos
  have hAflat (w : X dim) (hw : w ∈ (univ : Set (X dim))) (i j : I dim) :
      (1 : Mat dim) i j = divergenceCoeff m w i j := by
    simp [m,flatBallMetric,divergenceCoeff,chartVolume]
  have hU : FixedBallSolution m f.1 (S f).flat.1 := by
    refine ⟨(S f).flat.2,(S f).flatTrace,?_⟩
    intro w hw
    have h := negativeBallDivergence_eq_neg_laplace isOpen_univ hm hAflat (S f).flat.2.contDiffOn (mem_univ w)
    rw [(S f).flatEquation hw] at h
    have hμ : 0 < chartVolume m w := Real.sqrt_pos.2 (hm.2 w (mem_univ w)).det_pos
    exact (mul_eq_zero.mp (neg_eq_zero.mp h.symm)).resolve_left hμ.ne'
  have hP := fixedBallPoisson_solution isOpen_univ (subset_univ _) hm (d:=f.1)
    ⟨univ,isOpen_univ,subset_univ _,f.2.contDiffOn⟩
  have hE := eqOn_fderiv_closedUnitBall hU.1 hP.1
    (eqOn_fixedBallSolution isOpen_univ (subset_univ _) hm hU hP (fun _ _ => rfl))
  change (smoothTraceFlatDegree hA hEll S (smoothSphereTrace f)).1 z = _
  rw [smoothTraceFlatDegree_apply,smoothSphereTrace_apply]
  have hVal : (S f).degree.1 z = fderiv ℝ (S f).flat.1 z z := rfl
  rw [hVal,hE (sphere_subset_closedBall z.property)]
  unfold parametricBallConormal
  dsimp only
  change _ = ballConormal m (fixedBallPoisson m f.1) (sphereNormalize z)
  rw [sphereNormalize_eq_of_sphere z.property,ballConormal_flat one_pos,one_pow,one_mul]

theorem smoothSupportedTraceFiberRegular_flatDegree (Y : Set (X dim)) :
    SmoothSupportedTraceFiberRegular Y (fun _ => smoothTraceFlatDegree hA hEll S) := by
  intro u
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  refine ⟨univ ×ˢ ({0}ᶜ : Set (X dim)),parametricBallConormal
    (fun _ => flatBallMetric 1 (0:X dim)) G,
    isOpen_univ.prod isClosed_singleton.isOpen_compl,?_,
    contDiffOn_parametricFlatBallConormal G hG,?_⟩
  · intro q hq
    refine ⟨mem_univ _,?_⟩
    have h := mem_sphere_zero_iff_norm.mp hq.2
    exact fun hz => by
      change q.2 = 0 at hz
      rw [hz,norm_zero] at h
      exact zero_ne_one h
  · intro x hx z
    let f : SmoothData dim := ⟨fun w => G (x,w),hG.comp (contDiff_const.prodMk contDiff_id)⟩
    have hF : smoothSupportedTraceFiberL x u = smoothSphereTrace f :=
      Subtype.ext (funext (hu x))
    rw [hF]
    exact (smoothTraceFlatDegree_eq_parametricFlatBallConormal hA hEll S G hG x z).symm

end CalderonN
