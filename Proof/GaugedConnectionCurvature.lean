import Proof.CurvatureOperatorBounds
import Mathlib.Tactic.NoncommRing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

private lemma base_gauge_curvature_algebra
    (L A B P Q dA dB dP dQ : X →L[ℝ] X)
    (h : (L*A-P*L)*B+L*dB-(dQ*L+Q*(L*A-P*L))=
      (L*B-Q*L)*A+L*dA-(dP*L+P*(L*B-Q*L))) :
    L*(dB-dA+A*B-B*A)=(dQ-dP+P*Q-Q*P)*L := by
  apply sub_eq_zero.mp
  calc
    _ = ((L*A-P*L)*B+L*dB-(dQ*L+Q*(L*A-P*L)))-
        ((L*B-Q*L)*A+L*dA-(dP*L+P*(L*B-Q*L))) := by noncomm_ring
    _ = 0 := sub_eq_zero.mpr h

lemma fderiv_connection_apply_const (A : X → X →L[ℝ] X →L[ℝ] X) (y a b : X)
    (hA : DifferentiableAt ℝ A y) :
    fderiv ℝ (fun x => A x b) y a=fderiv ℝ A y a b := by
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    _root_.zero_apply,map_zero,zero_add] using
    DFunLike.congr_fun (hA.hasFDerivAt.clm_apply (hasFDerivAt_const b y)).fderiv a

lemma fderiv_base_operator_comp (A B : X → X →L[ℝ] X) (y a : X)
    (hA : DifferentiableAt ℝ A y) (hB : DifferentiableAt ℝ B y) :
    fderiv ℝ (fun x => (A x).comp (B x)) y a=
      (fderiv ℝ A y a).comp (B y)+(A y).comp (fderiv ℝ B y a) := by
  rw [fderiv_clm_comp hA hB]
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

/-- Curvature intertwines under a genuine frame transport equation.
All ring algebra here is on bounded endomorphisms of the finite-dimensional
base space X; no angular Sobolev operator is treated as an endomorphism. -/
theorem gauged_connection_curvature_intertwine {Y : Set X} (hY : IsOpen Y)
    (Γ Ω : X → X →L[ℝ] X →L[ℝ] X) (L : X → X →L[ℝ] X)
    (hΓ : ContDiffOn ℝ ∞ Γ Y) (hΩ : ContDiffOn ℝ ∞ Ω Y) (hL : ContDiffOn ℝ ∞ L Y)
    (hTransport : ∀ x ∈ Y,∀ a : X,fderiv ℝ L x a=(L x).comp (Ω x a)-(Γ x a).comp (L x))
    {y : X} (hy : y ∈ Y) (a b : X) :
    (L y).comp (curvatureLinear Ω y a b)=(curvatureLinear Γ y a b).comp (L y) := by
  have hLA := hL.contDiffAt (hY.mem_nhds hy)
  have hLD := hLA.differentiableAt (by simp)
  have hΓD := (hΓ.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hΩD := (hΩ.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hΓb (c : X) : DifferentiableAt ℝ (fun x => Γ x c) y := hΓD.clm_apply (differentiableAt_const c)
  have hΩb (c : X) : DifferentiableAt ℝ (fun x => Ω x c) y := hΩD.clm_apply (differentiableAt_const c)
  have hDb (v w : X) : fderiv ℝ (fun x => fderiv ℝ L x w) y v=
      (fderiv ℝ L y v).comp (Ω y w)+(L y).comp (fderiv ℝ (fun x => Ω x w) y v)-
        ((fderiv ℝ (fun x => Γ x w) y v).comp (L y)+(Γ y w).comp (fderiv ℝ L y v)) := by
    have hEq : (fun x => fderiv ℝ L x w) =ᶠ[𝓝 y]
        (fun x => (L x).comp (Ω x w)-(Γ x w).comp (L x)) := by
      filter_upwards [hY.mem_nhds hy] with x hx
      exact hTransport x hx w
    rw [hEq.fderiv_eq,fderiv_fun_sub (hLD.clm_comp (hΩb w)) ((hΓb w).clm_comp hLD)]
    simp only [_root_.sub_apply]
    rw [fderiv_base_operator_comp L (fun x => Ω x w) y v hLD (hΩb w),
      fderiv_base_operator_comp (fun x => Γ x w) L y v (hΓb w) hLD]
  have hDL : DifferentiableAt ℝ (fderiv ℝ L) y :=
    (hLA.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hSym : fderiv ℝ (fun x => fderiv ℝ L x b) y a=
      fderiv ℝ (fun x => fderiv ℝ L x a) y b := by
    rw [fderiv_connection_apply_const (fderiv ℝ L) y a b hDL,
      fderiv_connection_apply_const (fderiv ℝ L) y b a hDL]
    exact (hLA.isSymmSndFDerivAt (by simp)).eq a b
  have hKey := (hDb a b).symm.trans (hSym.trans (hDb b a))
  rw [hTransport y hy a,hTransport y hy b,
    fderiv_connection_apply_const Ω y a b hΩD,fderiv_connection_apply_const Ω y b a hΩD,
    fderiv_connection_apply_const Γ y a b hΓD,fderiv_connection_apply_const Γ y b a hΓD] at hKey
  unfold curvatureLinear
  exact base_gauge_curvature_algebra (L y) (Ω y a) (Ω y b) (Γ y a) (Γ y b)
    ((fderiv ℝ Ω y b) a) ((fderiv ℝ Ω y a) b)
    ((fderiv ℝ Γ y b) a) ((fderiv ℝ Γ y a) b) hKey

end ShrinkingSpheres
