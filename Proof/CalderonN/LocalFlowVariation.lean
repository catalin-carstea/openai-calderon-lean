module

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Prod

/- Local versions of the selected archive's MixedFlowDerivatives and the parameter
   variation step of SmoothFlowLinearization. The proof uses only the smooth germ
   at the evaluation point; no globally chosen flow is imposed on the actual map. -/
@[expose] public section

noncomputable section
set_option autoImplicit false
open Filter
open scoped ContDiff Topology
namespace CalderonN
variable {E G P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma hasDerivAt_prod_fst {f : ℝ → E × G} {v : E × G} {t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => (f s).1) v.1 t := by
  exact (ContinuousLinearMap.fst ℝ E G).hasFDerivAt.comp_hasDerivAt t hf

lemma hasDerivAt_prod_snd {f : ℝ → E × G} {v : E × G} {t : ℝ} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => (f s).2) v.2 t := by
  exact (ContinuousLinearMap.snd ℝ E G).hasFDerivAt.comp_hasDerivAt t hf

lemma fderiv_apply_const_of_contDiffAt (F : P → G) (p d e : P)
    (hF : ContDiffAt ℝ ∞ F p) :
    fderiv ℝ (fun x => fderiv ℝ F x d) p e = fderiv ℝ (fderiv ℝ F) p e d := by
  let L : (P →L[ℝ] G) →L[ℝ] G := ContinuousLinearMap.apply ℝ G d
  have hD : DifferentiableAt ℝ (fderiv ℝ F) p :=
    (hF.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have h := L.hasFDerivAt.comp p hD.hasFDerivAt
  exact congrArg (fun A : P →L[ℝ] G => A e) h.fderiv

lemma fderiv_base_slice_of_contDiffAt (F : E × ℝ → G) (a h : E) (t : ℝ)
    (hF : ContDiffAt ℝ ∞ F (a,t)) :
    fderiv ℝ (fun x => F (x,t)) a h = fderiv ℝ F (a,t) (h,0) := by
  have hs : HasFDerivAt (fun x : E => (x,t)) (ContinuousLinearMap.inl ℝ E ℝ) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const t a)
  have hc := (hF.differentiableAt (by simp)).hasFDerivAt.comp a hs
  exact congrArg (fun A : E →L[ℝ] G => A h) hc.fderiv

lemma hasDerivAt_base_derivative_in_time_local (F : E × ℝ → G) (a h : E) (t : ℝ)
    (hF : ContDiffAt ℝ ∞ F (a,t)) :
    HasDerivAt (fun s => fderiv ℝ F (a,s) (h,0))
      (fderiv ℝ (fun x => fderiv ℝ F (x,t) (0,1)) a h) t := by
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ F) (a,t) := hF.fderiv_right (by simp)
  let L : ((E × ℝ) →L[ℝ] G) →L[ℝ] G := ContinuousLinearMap.apply ℝ G (h,0)
  have htime := (L.hasFDerivAt.comp (a,t) (hD.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt t
    ((show HasDerivAt (fun _ : ℝ => a) 0 t from hasDerivAt_const _ _).prodMk (hasDerivAt_id t))
  have hslice : HasFDerivAt (fun x : E => (x,t)) (ContinuousLinearMap.inl ℝ E ℝ) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const t a)
  let T : ((E × ℝ) →L[ℝ] G) →L[ℝ] G := ContinuousLinearMap.apply ℝ G (0,1)
  have hbase : DifferentiableAt ℝ (fun p : E × ℝ => fderiv ℝ F p (0,1)) (a,t) :=
    T.differentiableAt.comp (a,t) (hD.differentiableAt (by simp))
  have heq : fderiv ℝ (fun x => fderiv ℝ F (x,t) (0,1)) a h =
      fderiv ℝ (fderiv ℝ F) (a,t) (h,0) (0,1) := by
    change fderiv ℝ ((fun p : E × ℝ => fderiv ℝ F p (0,1)) ∘ (fun x => (x,t))) a h = _
    rw [fderiv_comp a hbase hslice.differentiableAt,hslice.fderiv]
    exact fderiv_apply_const_of_contDiffAt F (a,t) (0,1) (h,0) hF
  rw [heq]
  have ht : HasDerivAt (fun s => fderiv ℝ F (a,s) (h,0))
      (fderiv ℝ (fderiv ℝ F) (a,t) (0,1) (h,0)) t := by
    simpa only [L,Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply] using htime
  exact ht.congr_deriv ((hF.isSymmSndFDerivAt (by simp)).eq (0,1) (h,0))

lemma hasDerivAt_time_slice (F : E × ℝ → G) (a : E) (t : ℝ)
    (hF : DifferentiableAt ℝ F (a,t)) :
    HasDerivAt (fun s => F (a,s)) (fderiv ℝ F (a,t) (0,1)) t := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t a).prodMk (hasDerivAt_id t))
  simpa only [Function.comp_def,Function.id_def] using hd

lemma hasDerivAt_time_derivative (F : E × ℝ → G) (a : E) (t : ℝ)
    (hF : ContDiffAt ℝ ∞ F (a,t)) :
    HasDerivAt (fun s => fderiv ℝ F (a,s) (0,1))
      (fderiv ℝ (fderiv ℝ F) (a,t) (0,1) (0,1)) t := by
  have hD := (hF.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hd := (hasDerivAt_time_slice (fderiv ℝ F) a t hD).clm_apply
    (hasDerivAt_const t ((0:E),(1:ℝ)))
  simpa only [map_zero,add_zero] using hd

lemma second_deriv_time_slice (F : E × ℝ → G) (a : E) (t : ℝ)
    (hF : ContDiffAt ℝ ∞ F (a,t)) :
    deriv (deriv (fun s => F (a,s))) t = fderiv ℝ (fderiv ℝ F) (a,t) (0,1) (0,1) := by
  have hNear := (hF.of_le (show (1:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have heq : deriv (fun s => F (a,s)) =ᶠ[𝓝 t] (fun s => fderiv ℝ F (a,s) (0,1)) := by
    have hpre := (continuous_const.prodMk continuous_id).continuousAt.eventually hNear
    filter_upwards [hpre] with s hs
    exact (hasDerivAt_time_slice F a s (hs.differentiableAt (by simp))).deriv
  exact heq.deriv_eq.trans (hasDerivAt_time_derivative F a t hF).deriv

/-- The parameter derivative of any local smooth ODE family satisfies its actual
    variational equation. Only the ODE germ in the parameter is needed at this time. -/
theorem hasDerivAt_parameter_variation (F : E × ℝ → G) (V : G → G) (a h : E) (t : ℝ)
    (hF : ContDiffAt ℝ ∞ F (a,t)) (hV : DifferentiableAt ℝ V (F (a,t)))
    (hODE : (fun x => fderiv ℝ F (x,t) (0,1)) =ᶠ[𝓝 a] (fun x => V (F (x,t)))) :
    HasDerivAt (fun s => fderiv ℝ F (a,s) (h,0))
      (fderiv ℝ V (F (a,t)) (fderiv ℝ F (a,t) (h,0))) t := by
  have hm := hasDerivAt_base_derivative_in_time_local F a h t hF
  have hs : DifferentiableAt ℝ (fun x => F (x,t)) a :=
    (hF.comp a (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hc := hV.hasFDerivAt.comp a hs.hasFDerivAt
  have hj : fderiv ℝ (fun x => fderiv ℝ F (x,t) (0,1)) a h =
      fderiv ℝ V (F (a,t)) (fderiv ℝ F (a,t) (h,0)) := by
    rw [hODE.fderiv_eq]
    change fderiv ℝ (V ∘ (fun x => F (x,t))) a h = _
    rw [hc.fderiv,ContinuousLinearMap.comp_apply,fderiv_base_slice_of_contDiffAt F a h t hF]
  exact hm.congr_deriv hj

end CalderonN
