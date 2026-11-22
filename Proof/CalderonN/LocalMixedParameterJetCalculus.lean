module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.LocalFlowVariation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-! Mixed parameter and time differentiation, adapted from the checked
Proposition 5.3 release f308cb9d. -/

public section

set_option autoImplicit false
noncomputable section
open Set Function Filter
open scoped Topology ContDiff BigOperators

namespace CalderonN

variable {E V P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

@[expose] def radialFirstDerivative (F : P × ℝ → V) (p : P × ℝ) : V :=
  fderiv ℝ F p (0,1)

theorem contDiff_radialFirstDerivative (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialFirstDerivative F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

def fixedDirectionalDerivative (F : E → V) (v : E) (x : E) : V :=
  fderiv ℝ F x v

theorem contDiff_fixedDirectionalDerivative (F : E → V) (hF : ContDiff ℝ ∞ F) (v : E) :
    ContDiff ℝ ∞ (fixedDirectionalDerivative F v) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

 
theorem fixedDirectionalDerivative_commute (F : E → V) (hF : ContDiff ℝ ∞ F) (v w : E) :
    fixedDirectionalDerivative (fixedDirectionalDerivative F v) w =
      fixedDirectionalDerivative (fixedDirectionalDerivative F w) v := by
  funext x
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  change (fderiv ℝ (fun y => fderiv ℝ F y v) x) w =
    (fderiv ℝ (fun y => fderiv ℝ F y w) x) v
  rw [fderiv_clm_apply hDF (differentiableAt_const v),
    fderiv_clm_apply hDF (differentiableAt_const w)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    ((hF.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq w v

 
def fixedJetEval : (j : ℕ) → (Fin j → E) → (E → V) → E → V
  | 0, _, F => F
  | j + 1, m, F =>
      fixedDirectionalDerivative (fixedJetEval j (Fin.tail m) F) (m 0)

theorem contDiff_fixedJetEval (j : ℕ) (m : Fin j → E) (F : E → V)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fixedJetEval j m F) := by
  induction j with
  | zero => simpa only [fixedJetEval] using hF
  | succ j ih =>
      exact contDiff_fixedDirectionalDerivative _ (ih (Fin.tail m)) (m 0)

theorem fixedJetEval_eq_iteratedFDeriv (j : ℕ) (m : Fin j → E) (F : E → V)
    (hF : ContDiff ℝ ∞ F) :
    fixedJetEval j m F = fun x => iteratedFDeriv ℝ j F x m := by
  induction j with
  | zero =>
      funext x
      simp only [fixedJetEval, iteratedFDeriv_zero_apply]
  | succ j ih =>
      rw [fixedJetEval, ih (Fin.tail m)]
      funext x
      have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j F) x :=
        (hF.iteratedFDeriv_right (m := ∞) (by simp)).differentiable (by simp) x
      exact (hd.iteratedFDeriv_succ_apply_left' (m := m)).symm

 
theorem fixedDirectionalDerivative_fixedJetEval (j : ℕ) (m : Fin j → E)
    (F : E → V) (hF : ContDiff ℝ ∞ F) (v : E) :
    fixedDirectionalDerivative (fixedJetEval j m F) v =
      fixedJetEval j m (fixedDirectionalDerivative F v) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [fixedJetEval]
      rw [fixedDirectionalDerivative_commute _ (contDiff_fixedJetEval j (Fin.tail m) F hF)
        (m 0) v, ih (Fin.tail m)]

 
def parameterJetField (j : ℕ) (F : P × ℝ → V) (x : P × ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => P) V :=
  (iteratedFDeriv ℝ j F x).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inl ℝ P ℝ)

theorem contDiff_parameterJetField (j : ℕ) (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (parameterJetField j F) := by
  unfold parameterJetField
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin j => ContinuousLinearMap.inl ℝ P ℝ))).comp
        (hF.iteratedFDeriv_right (m := ∞) (by simp))

theorem parameterJetField_eq_iteratedFDeriv (j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ) :
    parameterJetField j F (p,r) = iteratedFDeriv ℝ j (fun q => F (q,r)) p := by
  have hc : ContDiff ℝ ∞ (fun z : P × ℝ => F ((0,r) + z)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have he : (fun q : P => F (q,r)) =
      (fun z : P × ℝ => F ((0,r) + z)) ∘ ContinuousLinearMap.inl ℝ P ℝ := by
    funext q
    simp
  rw [he, (ContinuousLinearMap.inl ℝ P ℝ).iteratedFDeriv_comp_right hc p (by simp)]
  rw [iteratedFDeriv_comp_add_left]
  simp [parameterJetField]

theorem parameterJetField_apply_eq_fixedJetEval (j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (m : Fin j → P) :
    (fun x => parameterJetField j F x m) =
      fixedJetEval j (fun i => (m i,0)) F := by
  rw [fixedJetEval_eq_iteratedFDeriv j _ F hF]
  funext x
  simp only [parameterJetField, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.inl_apply]

 

theorem radialFirstDerivative_parameterJetField (j : ℕ) (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) :
    radialFirstDerivative (parameterJetField j F) =
      parameterJetField j (radialFirstDerivative F) := by
  funext x
  ext m
  have hJ : DifferentiableAt ℝ (parameterJetField j F) x :=
    (contDiff_parameterJetField j F hF).differentiable (by simp) x
  calc
    radialFirstDerivative (parameterJetField j F) x m =
        fixedDirectionalDerivative (fun y => parameterJetField j F y m) (0,1) x := by
      symm
      exact fderiv_continuousMultilinear_apply_const_apply hJ m (0,1)
    _ = fixedDirectionalDerivative (fixedJetEval j (fun i => (m i,0)) F) (0,1) x := by
      rw [parameterJetField_apply_eq_fixedJetEval j F hF m]
    _ = fixedJetEval j (fun i => (m i,0)) (radialFirstDerivative F) x := by
      change fixedDirectionalDerivative (fixedJetEval j (fun i => (m i,0)) F) (0,1) x =
        fixedJetEval j (fun i => (m i,0)) (fixedDirectionalDerivative F (0,1)) x
      rw [fixedDirectionalDerivative_fixedJetEval j _ F hF (0,1)]
    _ = parameterJetField j (radialFirstDerivative F) x m :=
      (congrFun (parameterJetField_apply_eq_fixedJetEval j _
        (contDiff_radialFirstDerivative F hF) m) x).symm

 
variable [FiniteDimensional ℝ P]

theorem exists_global_smooth_germ_of_open (F : P → V) {U : Set P}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {x : P} (hx : x ∈ U) :
    ∃ G : P → V, ContDiff ℝ ∞ G ∧ G =ᶠ[𝓝 x] F := by
  obtain ⟨G,hG,_,W,hW,hxW,_,he⟩ := exists_contDiff_extension_near_compact
    hU (isCompact_singleton (x:=x)) (singleton_subset_iff.mpr hx) hF
  refine ⟨G,hG,?_⟩
  filter_upwards [hW.mem_nhds (hxW (mem_singleton x))] with y hy
  exact he hy

theorem parameterJetField_congr_nhds (n : ℕ) {F G : P × ℝ → V} {x : P × ℝ}
    (he : F =ᶠ[𝓝 x] G) :
    parameterJetField n F =ᶠ[𝓝 x] parameterJetField n G := by
  filter_upwards [he.iteratedFDeriv ℝ n] with q hq
  exact congrArg (fun A => A.compContinuousLinearMap
    (fun _ : Fin n => ContinuousLinearMap.inl ℝ P ℝ)) hq

theorem radialFirstDerivative_congr_nhds {F G : P × ℝ → V} {x : P × ℝ}
    (he : F =ᶠ[𝓝 x] G) :
    radialFirstDerivative F =ᶠ[𝓝 x] radialFirstDerivative G := by
  filter_upwards [he.fderiv (𝕜:=ℝ)] with q hq
  exact congrArg (fun A : (P × ℝ) →L[ℝ] V => A (0,1)) hq

theorem parameterJetField_eq_iteratedFDeriv_of_open (n : ℕ) (F : P × ℝ → V)
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (t : ℝ) (hp : (p,t) ∈ U) :
    parameterJetField n F (p,t) = iteratedFDeriv ℝ n (fun q => F (q,t)) p := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hp
  have hSlice : (fun q => G (q,t)) =ᶠ[𝓝 p] (fun q => F (q,t)) :=
    he.comp_tendsto ((continuousAt_id.prodMk continuousAt_const).tendsto)
  rw [← (parameterJetField_congr_nhds n he).eq_of_nhds,
    parameterJetField_eq_iteratedFDeriv n G hG p t]
  exact (hSlice.iteratedFDeriv ℝ n).eq_of_nhds

theorem contDiffAt_parameterJetField_of_open (n : ℕ) (F : P × ℝ → V)
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {x : P × ℝ} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (parameterJetField n F) x := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hx
  exact (contDiff_parameterJetField n G hG).contDiffAt.congr_of_eventuallyEq
    (parameterJetField_congr_nhds n he).symm

/-- Mixed time/parameter differentiation is local on an explicit smooth open
    domain. No global extension contributes any quantitative bound. -/
theorem hasDerivAt_parameterJetField_of_open (n : ℕ) (F : P × ℝ → V)
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (t : ℝ) (hp : (p,t) ∈ U) :
    HasDerivAt (fun s => parameterJetField n F (p,s))
      (iteratedFDeriv ℝ n (fun q => radialFirstDerivative F (q,t)) p) t := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hp
  have hJ := parameterJetField_congr_nhds n he
  have hSlice : (fun s => parameterJetField n G (p,s)) =ᶠ[𝓝 t]
      (fun s => parameterJetField n F (p,s)) :=
    hJ.comp_tendsto ((continuousAt_const.prodMk continuousAt_id).tendsto)
  have hRad : (fun q => radialFirstDerivative G (q,t)) =ᶠ[𝓝 p]
      (fun q => radialFirstDerivative F (q,t)) :=
    (radialFirstDerivative_congr_nhds he).comp_tendsto
      ((continuousAt_id.prodMk continuousAt_const).tendsto)
  have hd := hasDerivAt_time_slice (parameterJetField n G) p t
    ((contDiff_parameterJetField n G hG).differentiable (by simp) (p,t))
  change HasDerivAt (fun s => parameterJetField n G (p,s))
    (radialFirstDerivative (parameterJetField n G) (p,t)) t at hd
  rw [radialFirstDerivative_parameterJetField n G hG,
    parameterJetField_eq_iteratedFDeriv n _ (contDiff_radialFirstDerivative G hG) p t,
    (hRad.iteratedFDeriv ℝ n).eq_of_nhds] at hd
  exact hd.congr_of_eventuallyEq hSlice.symm

end CalderonN
