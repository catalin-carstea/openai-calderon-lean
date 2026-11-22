module

public import Proof.CalderonN.MovingGreenConormalComparison

import Proof.CalderonN.CoordinateJets
import Mathlib.Tactic

/-! Adapted from `WeightedGreenHorizontal` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 300000

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- A radius-weighted horizontal derivative uses one weighted base jet
and one ordinary angular jet of the normalized conormal. -/
theorem norm_weighted_horizontal_normalGreenAngularLift_le
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) (lam : ℝ)
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) (i : (I dim)) (q : (X dim) × (X dim))
    {R D M B : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hrBound : |r q.1| ≤ R) (hr₁ : |coordDeriv i r q.1| ≤ D)
    (hConn : ‖connection γ q.1 (axis i) q.2‖ ≤ M)
    (hFrame : ‖fderiv ℝ (fun z => (movingBallToFrame γ e z).2) q‖ ≤ M)
    {f : (NormalGreenParameter dim) × (X dim) → ℝ}
    (hf : DifferentiableAt ℝ f (normalGreenAngularLift γ e lam r q))
    (hBase : ∀ v : (NormalGreenParameter dim),
      ‖fderiv ℝ (fun p => f (p,(normalGreenAngularLift γ e lam r q).2))
        (normalGreenAngularLift γ e lam r q).1 (r q.1 • v)‖ ≤ B*‖v‖)
    (hAngle : ‖fderiv ℝ (fun w => f ((normalGreenAngularLift γ e lam r q).1,w))
      (normalGreenAngularLift γ e lam r q).2‖ ≤ B) :
    ‖(r q.1 : ℂ)*horizontal γ (fun z => (f (normalGreenAngularLift γ e lam r z) : ℂ))
        q.1 q.2 (axis i)‖ ≤ B*(max 1 D+R*M^2) := by
  let L := normalGreenAngularLift γ e lam r
  let d : (X dim) × (X dim) := (axis i,-connection γ q.1 (axis i) q.2)
  let W (z : (X dim) × (X dim)) := (movingBallToFrame γ e z).2
  let v : (NormalGreenParameter dim) := (0,(axis i,coordDeriv i r q.1))
  let a := fderiv ℝ W q d
  have hD₀ : ‖d‖ ≤ M := by
    rw [Prod.norm_def,norm_axis,norm_neg]
    exact max_le hM hConn
  have hA : ‖a‖ ≤ M^2 :=
    ((fderiv ℝ W q).le_opNorm d).trans
      ((mul_le_mul hFrame hD₀ (norm_nonneg _) (zero_le_one.trans hM)).trans_eq (by ring))
  have hv : ‖v‖ ≤ max 1 D := by
    simp only [v,Prod.norm_def,norm_zero,norm_axis,Real.norm_eq_abs,max_le_iff]
    exact ⟨zero_le_one.trans (le_max_left _ _),le_max_left _ _,hr₁.trans (le_max_right _ _)⟩
  let F := ContinuousLinearMap.fst ℝ (X dim) (X dim)
  have hRder := (hr.differentiable (by simp) q.1).hasFDerivAt.comp q F.hasFDerivAt
  have hWder := ((contDiff_movingBallToFrame hγ he).snd.differentiable (by simp) q).hasFDerivAt
  have hL := ((hasFDerivAt_const (c := lam) q).prodMk (F.hasFDerivAt.prodMk hRder)).prodMk hWder
  have hL' : fderiv ℝ L q d = (v,a) := by
    have h := congrArg (fun A : (X dim) × (X dim) →L[ℝ] (NormalGreenParameter dim) × (X dim) => A d) hL.fderiv
    change fderiv ℝ L q d = (v,a) at h
    exact h
  have hfd := hf.hasFDerivAt
  change HasFDerivAt f (fderiv ℝ f (L q)) ((L q).1,(L q).2) at hfd
  have hBaseD := (hfd.comp (L q).1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) (L q).1 (L q).2)).fderiv
  have hAngD := (hfd.comp (L q).2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) (L q).1 (L q).2)).fderiv
  have hU := (Complex.ofRealCLM.hasFDerivAt.comp q
    (hf.hasFDerivAt.comp q ((contDiff_normalGreenAngularLift hγ he lam hr).differentiable (by simp) q).hasFDerivAt)).fderiv
  change ‖(r q.1 : ℂ) * fderiv ℝ (Complex.ofRealCLM ∘ f ∘ L) q d‖ ≤ _
  rw [hU]
  change ‖(r q.1 : ℂ) * (fderiv ℝ f (L q) (fderiv ℝ L q d) : ℂ)‖ ≤ _
  rw [hL',← Complex.ofReal_mul,Complex.norm_real,← smul_eq_mul,← map_smul]
  have hSplit : r q.1 • (v,a) = (r q.1 • v,0)+(0,r q.1 • a) := by simp
  rw [hSplit,map_add]
  have hBase' : ‖fderiv ℝ f (L q) (r q.1 • v,0)‖ ≤ B*‖v‖ := by
    have h := hBase v
    change ‖fderiv ℝ (f ∘ fun p => (p,(L q).2)) (L q).1 (r q.1 • v)‖ ≤ B*‖v‖ at h
    rw [hBaseD] at h
    exact h
  have hAngle' : ‖fderiv ℝ f (L q) (0,r q.1 • a)‖ ≤ B*(R*M^2) := by
    have h := hAngle
    change ‖fderiv ℝ (f ∘ fun w => ((L q).1,w)) (L q).2‖ ≤ B at h
    rw [hAngD] at h
    calc
      _ ≤ ‖(fderiv ℝ f (L q)).comp (ContinuousLinearMap.inr ℝ (NormalGreenParameter dim) (X dim))‖ *
          ‖r q.1 • a‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B*(R*M^2) := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul h (mul_le_mul hrBound hA (norm_nonneg _) hR)
          (by positivity) hB
  exact (norm_add_le _ _).trans ((add_le_add
    (hBase'.trans (mul_le_mul_of_nonneg_left hv hB)) hAngle').trans_eq (by ring))

end CalderonN
