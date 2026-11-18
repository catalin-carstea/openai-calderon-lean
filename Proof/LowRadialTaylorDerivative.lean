import Proof.RectangularImplicitOperatorDerivative
import Proof.PoissonTaylorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open scoped Topology
namespace ShrinkingSpheres

/-- The exact boundary correction terms in the radial Taylor left identity
    retain a quadratic derivative when their actual factors have these bounds. -/
theorem norm_radial_taylor_rhs_derivative_le
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (NQ B : P → E →L[ℝ] F) (MQ M : P → F →L[ℝ] F)
    (T : Fin 3 → P → F →L[ℝ] F) (D : E →L[ℝ] F) (G : Fin 3 → E →L[ℝ] F)
    (x : P) (c r DN DQ DT DM VM VB DB : ℝ)
    (hNQ : DifferentiableAt ℝ NQ x) (hB : DifferentiableAt ℝ B x)
    (hMQ : DifferentiableAt ℝ MQ x) (hM : DifferentiableAt ℝ M x)
    (hT : ∀ j,DifferentiableAt ℝ (T j) x)
    (hr : 0 ≤ r) (hDN : 0 ≤ DN) (hDQ : 0 ≤ DQ) (hDT : 0 ≤ DT)
    (hDM : 0 ≤ DM) (hVM : 0 ≤ VM) (hVB : 0 ≤ VB) (hDB : 0 ≤ DB)
    (hNN : ‖fderiv ℝ NQ x‖ ≤ DN*r^2) (hNQ' : ‖fderiv ℝ MQ x‖ ≤ DQ*r^2)
    (hNT : ∀ j,‖fderiv ℝ (T j) x‖ ≤ DT*r^2)
    (hNM : ‖fderiv ℝ M x‖ ≤ DM*r) (hVDiff : ‖M x-c • ContinuousLinearMap.id ℝ F‖ ≤ VM*r)
    (hNB : ‖B x‖ ≤ VB) (hDB' : ‖fderiv ℝ B x‖ ≤ DB) :
    ‖fderiv ℝ (fun p => NQ p-(MQ p).comp D-∑ j : Fin 3,(T j p).comp (G j)-
      r • (M p-c • ContinuousLinearMap.id ℝ F).comp (B p)) x‖ ≤
        (DN+DQ*‖D‖+DT*∑ j : Fin 3,‖G j‖+DM*VB+VM*DB)*r^2 := by
  let MD := fun p => M p-c • ContinuousLinearMap.id ℝ F
  let S := fun p => ∑ j : Fin 3,(T j p).comp (G j)
  let Q := fun p => (MQ p).comp D
  let C := fun p => (MD p).comp (B p)
  have hMD : DifferentiableAt ℝ MD x := hM.sub_const _
  have hS : DifferentiableAt ℝ S x := DifferentiableAt.fun_sum (u:=Finset.univ)
    (fun j _ => (hT j).clm_comp (differentiableAt_const (G j)))
  have hQ : DifferentiableAt ℝ Q x := hMQ.clm_comp (differentiableAt_const D)
  have hC : DifferentiableAt ℝ C x := hMD.clm_comp hB
  have hDQBound := norm_fderiv_clm_comp_le MQ (fun _ : P => D) x hMQ (differentiableAt_const D)
  simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero] at hDQBound
  have hQN : ‖fderiv ℝ Q x‖ ≤ (DQ*r^2)*‖D‖ :=
    hDQBound.trans (mul_le_mul_of_nonneg_right hNQ' (norm_nonneg _))
  have hCN := norm_fderiv_clm_comp_le MD B x hMD hB
  have hMDNorm : ‖fderiv ℝ MD x‖ ≤ DM*r := by rw [show MD = fun p => M p-c • ContinuousLinearMap.id ℝ F from rfl,fderiv_sub_const];exact hNM
  have hCross : ‖fderiv ℝ C x‖ ≤ (DM*r)*VB+(VM*r)*DB :=
    hCN.trans (add_le_add (mul_le_mul hMDNorm hNB (norm_nonneg _) (mul_nonneg hDM hr))
      (mul_le_mul hVDiff hDB' (norm_nonneg _) (mul_nonneg hVM hr)))
  have hSumDerivative := (HasFDerivAt.sum (fun j (_ : j ∈ Finset.univ) =>
    ((hT j).clm_comp (differentiableAt_const (G j))).hasFDerivAt)).fderiv
  change fderiv ℝ S x = ∑ j : Fin 3,fderiv ℝ (fun p => (T j p).comp (G j)) x at hSumDerivative
  have hSN : ‖fderiv ℝ S x‖ ≤ DT*(∑ j : Fin 3,‖G j‖)*r^2 := by
    rw [hSumDerivative]
    calc
      _ ≤ ∑ j : Fin 3,‖fderiv ℝ (fun p => (T j p).comp (G j)) x‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin 3,(DT*r^2)*‖G j‖ := Finset.sum_le_sum (fun j _ => by
        have h := norm_fderiv_clm_comp_le (T j) (fun _ : P => G j) x (hT j) (differentiableAt_const _)
        simp only [fderiv_const_apply,norm_zero,mul_zero,add_zero] at h
        exact h.trans (mul_le_mul_of_nonneg_right (hNT j) (norm_nonneg _)))
      _ = _ := by rw [← Finset.mul_sum];ring
  have hFull := (((hNQ.hasFDerivAt.sub hQ.hasFDerivAt).sub hS.hasFDerivAt).sub
    (hC.hasFDerivAt.const_smul r)).fderiv
  change fderiv ℝ (fun p => NQ p-Q p-S p-r • C p) x = _ at hFull
  change ‖fderiv ℝ (fun p => NQ p-Q p-S p-r • C p) x‖ ≤ _
  rw [hFull]
  calc
    _ ≤ ‖fderiv ℝ NQ x‖+‖fderiv ℝ Q x‖+‖fderiv ℝ S x‖+‖r • fderiv ℝ C x‖ :=
      (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) (le_refl _))) (le_refl _))
    _ ≤ DN*r^2+(DQ*r^2)*‖D‖+DT*(∑ j : Fin 3,‖G j‖)*r^2+r*((DM*r)*VB+(VM*r)*DB) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
      exact add_le_add (add_le_add (add_le_add hNN hQN) hSN) (mul_le_mul_of_nonneg_left hCross hr)
    _ = _ := by ring

/-- The true radial left identity and the same inverse/point/derivative data
    give a quadratic derivative bound for the actual radial Taylor remainder. -/
theorem norm_radial_taylor_derivative_of_left_identity
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : P → F →L[ℝ] F) (J R : P → E →L[ℝ] F) (x : P) (r CI DM CJ DR : ℝ)
    (hM : DifferentiableAt ℝ M x) (hJ : DifferentiableAt ℝ J x)
    (hIdentity : (fun p => (M p).comp (J p)) =ᶠ[𝓝 x] R)
    (hInv : (M x).IsInvertible) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCI : 0 ≤ CI) (hDM : 0 ≤ DM) (hCJ : 0 ≤ CJ) (hDR : 0 ≤ DR)
    (hNI : ‖(M x).inverse‖ ≤ CI) (hDM' : ‖fderiv ℝ M x‖ ≤ DM*r)
    (hCJ' : ‖J x‖ ≤ CJ*r^2) (hDR' : ‖fderiv ℝ R x‖ ≤ DR*r^2) :
    ‖fderiv ℝ J x‖ ≤ CI*(DR+DM*CJ)*r^2 := by
  have hBound := norm_operator_derivative_of_rectangular_left_identity M J R x hM hJ hIdentity hInv
    CI (DM*r) (CJ*r^2) (DR*r^2) hCI (by positivity) (by positivity) (by positivity) hNI hDM' hCJ' hDR'
  refine hBound.trans ?_
  have hrr : r*r^2 ≤ r^2 := mul_le_of_le_one_left (sq_nonneg r) hr1
  have hle := mul_le_mul_of_nonneg_left hrr (mul_nonneg hDM hCJ)
  have hInner : DR*r^2+DM*r*(CJ*r^2) ≤ (DR+DM*CJ)*r^2 := by nlinarith only [hle]
  exact (mul_le_mul_of_nonneg_left hInner hCI).trans_eq (by ring)

end ShrinkingSpheres
