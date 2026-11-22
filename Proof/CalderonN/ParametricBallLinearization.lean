module

public import Proof.CalderonN.JointSmoothBallResponse
public import Proof.CalderonN.CenterDerivativeSlice

import Proof.CalderonN.MatrixFieldJetNorms
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Exact differentiation of the actual smooth Dirichlet family,
including its radial derivative at the boundary. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxSynthPendingDepth 31
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN
open BallDirichlet

variable {dim : ℕ} [NeZero dim]

@[expose] def ballParameterDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × X dim → E) (p : ℝ × X dim) : E := fderiv ℝ f p (1,0)

@[expose] def ballSpatialDerivative (v : X dim) (f : ℝ × X dim → ℝ)
    (p : ℝ × X dim) : ℝ := fderiv ℝ f p (0,v)

theorem contDiff_ballParameterDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × X dim → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (ballParameterDerivative f) :=
  (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

theorem contDiff_ballSpatialDerivative {f : ℝ × X dim → ℝ} (hf : ContDiff ℝ ∞ f) (v : X dim) :
    ContDiff ℝ ∞ (ballSpatialDerivative v f) :=
  (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_ballParameterDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × X dim → E} (hf : ContDiff ℝ ∞ f) (p : ℝ × X dim) :
    HasDerivAt (fun t => f (t,p.2)) (ballParameterDerivative f p) p.1 :=
  hasDerivAt_centerDerivativeSlice f p.2 p.1 (hf.differentiable (by simp) p)

theorem ballSpatialDerivative_slice {f : ℝ × X dim → ℝ} (hf : ContDiff ℝ ∞ f)
    (v : X dim) (p : ℝ × X dim) :
    ballSpatialDerivative v f p = fderiv ℝ (fun z => f (p.1,z)) p.2 v := by
  have hI : HasFDerivAt (fun z : X dim => (p.1,z))
      (ContinuousLinearMap.inr ℝ ℝ (X dim)) p.2 :=
    (hasFDerivAt_const (𝕜:=ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hd : HasFDerivAt f (fderiv ℝ f p) ((fun z : X dim => (p.1,z)) p.2) :=
    (hf.differentiable (by simp) p).hasFDerivAt
  have h : HasFDerivAt (fun z => f (p.1,z))
      ((fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ (X dim))) p.2 :=
    hd.comp p.2 hI
  exact congrArg (fun L : X dim →L[ℝ] ℝ => L v) h.fderiv.symm

theorem ballParameterDerivative_ballSpatialDerivative {f : ℝ × X dim → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : X dim) (p : ℝ × X dim) :
    ballParameterDerivative (ballSpatialDerivative v f) p =
      ballSpatialDerivative v (ballParameterDerivative f) p := by
  have hd := (hf.fderiv_right (m:=∞) (by simp)).differentiable (by simp) p
  have hEval (d : ℝ × X dim) :
      fderiv ℝ (fun q => fderiv ℝ f q d) p =
        (ContinuousLinearMap.apply ℝ ℝ d).comp (fderiv ℝ (fderiv ℝ f) p) :=
    ((ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp p hd.hasFDerivAt).fderiv
  change fderiv ℝ (fun q => fderiv ℝ f q (0,v)) p (1,0) =
    fderiv ℝ (fun q => fderiv ℝ f q (1,0)) p (0,v)
  rw [hEval,hEval]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq (1,0) (0,v)

theorem hasDerivAt_ballSpatialTrace {b : ℝ × X dim → ℝ} (hb : ContDiff ℝ ∞ b)
    (t : ℝ) (z v : X dim) :
    HasDerivAt (fun s => fderiv ℝ (fun x => b (s,x)) z v)
      (fderiv ℝ (fun x => ballParameterDerivative b (t,x)) z v) t := by
  have h := hasDerivAt_ballParameterDerivative (contDiff_ballSpatialDerivative hb v) (t,z)
  rw [ballParameterDerivative_ballSpatialDerivative hb v (t,z),
    ballSpatialDerivative_slice (contDiff_ballParameterDerivative hb) v (t,z)] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s =>
    (ballSpatialDerivative_slice hb v (s,z)).symm)

private theorem familyNegativeDivergence_eq_sum
    {a : ℝ × X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {b : ℝ × X dim → ℝ} (hb : ContDiff ℝ ∞ b) (t : ℝ) (z : X dim) :
    negativeBallDivergence (fun x => a (t,x)) (fun x => b (t,x)) z =
      -(∑ i : I dim, ∑ j : I dim, ballSpatialDerivative (axis i)
        (fun p => a p i j*ballSpatialDerivative (axis j) b p) (t,z)) := by
  let F (i j : I dim) (p : ℝ × X dim) := a p i j*ballSpatialDerivative (axis j) b p
  have hF (i j : I dim) : ContDiff ℝ ∞ (F i j) :=
    ((matrixEntryL i j).contDiff.comp ha).mul (contDiff_ballSpatialDerivative hb _)
  have hSlice (i j : I dim) :
      (fun x => F i j (t,x)) = fun x => a (t,x) i j*coordDeriv j (fun y => b (t,y)) x := by
    funext x
    change a (t,x) i j*ballSpatialDerivative (axis j) b (t,x) = _
    rw [ballSpatialDerivative_slice hb]
    rfl
  change negativeBallDivergence (fun x => a (t,x)) (fun x => b (t,x)) z =
    -(∑ i : I dim, ∑ j : I dim, ballSpatialDerivative (axis i) (F i j) (t,z))
  simp only [negativeBallDivergence,Elliptic.Lop,Elliptic.pd,coordDeriv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hs (j : I dim) : DifferentiableAt ℝ (fun x => F i j (t,x)) z :=
    ((hF i j).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z
  have hSum : (fun x => ∑ j : I dim, a (t,x) i j * fderiv ℝ (fun y => b (t,y)) x (axis j)) =
      (fun x => ∑ j : I dim, F i j (t,x)) := by
    funext x
    exact Finset.sum_congr rfl fun j _ => (congrFun (hSlice i j) x).symm
  rw [hSum,fderiv_fun_sum (fun j _ => hs j),ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => (ballSpatialDerivative_slice (hF i j) (axis i) (t,z)).symm

theorem hasDerivAt_negativeBallDivergence_family
    {a : ℝ × X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {b : ℝ × X dim → ℝ} (hb : ContDiff ℝ ∞ b) (t : ℝ) (z : X dim) :
    HasDerivAt (fun s => negativeBallDivergence (fun x => a (s,x)) (fun x => b (s,x)) z)
      (negativeBallDivergence (fun x => a (t,x)) (fun x => ballParameterDerivative b (t,x)) z +
        negativeBallDivergence (fun x => ballParameterDerivative a (t,x)) (fun x => b (t,x)) z) t := by
  let A (i j : I dim) (p : ℝ × X dim) := a p i j
  let B (j : I dim) := ballSpatialDerivative (axis j) b
  let F (i j : I dim) (p : ℝ × X dim) := A i j p*B j p
  have hA (i j : I dim) : ContDiff ℝ ∞ (A i j) :=
    (matrixEntryL i j).contDiff.comp ha
  have hB (j : I dim) := contDiff_ballSpatialDerivative hb (axis j)
  have hF (i j : I dim) := (hA i j).mul (hB j)
  have hBparam (j : I dim) (p : ℝ × X dim) :
      ballParameterDerivative (B j) p = ballSpatialDerivative (axis j) (ballParameterDerivative b) p :=
    ballParameterDerivative_ballSpatialDerivative hb (axis j) p
  have hAparam (i j : I dim) (p : ℝ × X dim) :
      ballParameterDerivative (A i j) p = ballParameterDerivative a p i j := by
    have h := (matrixEntryL i j).hasFDerivAt.comp_hasDerivAt p.1 (hasDerivAt_ballParameterDerivative ha p)
    exact (hasDerivAt_ballParameterDerivative (hA i j) p).unique h
  have hFparam (i j : I dim) : ballParameterDerivative (F i j) =
      fun p => A i j p*ballSpatialDerivative (axis j) (ballParameterDerivative b) p+
        ballParameterDerivative a p i j*B j p := by
    funext p
    have h := (hasDerivAt_ballParameterDerivative (hA i j) p).mul
      (hasDerivAt_ballParameterDerivative (hB j) p)
    have hh := (hasDerivAt_ballParameterDerivative (hF i j) p).unique h
    rw [hAparam,hBparam,add_comm] at hh
    exact hh
  let H (p : ℝ × X dim) := -(∑ i : I dim, ∑ j : I dim, ballSpatialDerivative (axis i) (F i j) p)
  have hH (s : ℝ) :
      H (s,z) = negativeBallDivergence (fun x => a (s,x)) (fun x => b (s,x)) z :=
    (familyNegativeDivergence_eq_sum ha hb s z).symm
  have hPer (i j : I dim) :
      HasDerivAt (fun s => ballSpatialDerivative (axis i) (F i j) (s,z))
        (ballSpatialDerivative (axis i) (ballParameterDerivative (F i j)) (t,z)) t := by
    have h := hasDerivAt_ballParameterDerivative (contDiff_ballSpatialDerivative (hF i j) (axis i)) (t,z)
    rwa [ballParameterDerivative_ballSpatialDerivative (hF i j) (axis i) (t,z)] at h
  have hE := (HasDerivAt.fun_sum (u:=Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u:=Finset.univ) fun j _ => hPer i j).neg
  have hh : HasDerivAt (fun s => H (s,z))
      (-(∑ i : I dim, ∑ j : I dim,
        ballSpatialDerivative (axis i) (ballParameterDerivative (F i j)) (t,z))) t := hE
  have hTarget : -(∑ i : I dim, ∑ j : I dim,
        ballSpatialDerivative (axis i) (ballParameterDerivative (F i j)) (t,z)) =
      negativeBallDivergence (fun x => a (t,x)) (fun x => ballParameterDerivative b (t,x)) z +
        negativeBallDivergence (fun x => ballParameterDerivative a (t,x)) (fun x => b (t,x)) z := by
    simp_rw [hFparam]
    have h₁ (i j : I dim) : ContDiff ℝ ∞ (fun p =>
        A i j p*ballSpatialDerivative (axis j) (ballParameterDerivative b) p) :=
      (hA i j).mul (contDiff_ballSpatialDerivative (contDiff_ballParameterDerivative hb) _)
    have h₂ (i j : I dim) : ContDiff ℝ ∞ (fun p => ballParameterDerivative a p i j*B j p) :=
      ((matrixEntryL i j).contDiff.comp (contDiff_ballParameterDerivative ha)).mul (hB j)
    have hAdd (i j : I dim) :
        ballSpatialDerivative (axis i)
          (fun p => A i j p*ballSpatialDerivative (axis j) (ballParameterDerivative b) p+
            ballParameterDerivative a p i j*B j p) (t,z) =
        ballSpatialDerivative (axis i)
          (fun p => A i j p*ballSpatialDerivative (axis j) (ballParameterDerivative b) p) (t,z)+
          ballSpatialDerivative (axis i)
            (fun p => ballParameterDerivative a p i j*B j p) (t,z) := by
      let g₁ (p : ℝ × X dim) := A i j p*ballSpatialDerivative (axis j) (ballParameterDerivative b) p
      let g₂ (p : ℝ × X dim) := ballParameterDerivative a p i j*B j p
      change fderiv ℝ (g₁+g₂) (t,z) (0,axis i) =
        fderiv ℝ g₁ (t,z) (0,axis i)+fderiv ℝ g₂ (t,z) (0,axis i)
      rw [fderiv_add ((h₁ i j).differentiable (by simp) _) ((h₂ i j).differentiable (by simp) _),add_apply]
    simp_rw [hAdd,Finset.sum_add_distrib,neg_add]
    rw [familyNegativeDivergence_eq_sum ha (contDiff_ballParameterDerivative hb) t z,
      familyNegativeDivergence_eq_sum (contDiff_ballParameterDerivative ha) hb t z]
  exact (hh.congr_deriv hTarget).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => (hH s).symm)

end CalderonN
