module

public import Proof.Manuscript.MovingTrace.PhysicalResidualEnvelopes
public import Proof.CalderonN.CompactFiniteJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 2800000

open CalderonN CalderonPaper Set Filter Finset
open scoped ContDiff Topology

namespace CalderonPatch.BoundaryLayer

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Evaluate the split operator on the angular/depth slice while keeping
the data and output smoothly parameterized by p. -/
def jointSplitOperator
    (A : (P × X n) × ℝ → Matrix (I n) (I n) ℂ)
    (τ : (P × X n) × ℝ → ℂ) (c : (P × X n) × ℝ → I n → ℂ)
    (V : (P × X n) × ℝ → ℂ) (q : (P × X n) × ℝ) : ℂ :=
  complexSplitOperator (A q) (τ q) (c q)
    (fun z : X n × ℝ => V ((q.1.1,z.1),z.2)) q.1.2 q.2

private theorem fderiv_split_tangent_joint {V : (P × X n) × ℝ → ℂ}
    (hV : ContDiff ℝ ∞ V) (p : P) (x : X n) (t : ℝ) (i : I n) :
    splitFirst (fun z : X n × ℝ => V ((p,z.1),z.2)) x t i =
      fderiv ℝ V ((p,x),t) ((0,axis i),0) := by
  let L := (ContinuousLinearMap.inl ℝ (P × X n) ℝ).comp (ContinuousLinearMap.inr ℝ P (X n))
  have hM : HasFDerivAt (fun y : X n => ((p,y),t)) L x := by
    have hs : HasFDerivAt (fun y : X n => (p,y)) (ContinuousLinearMap.inr ℝ P (X n)) x :=
      hasFDerivAt_prodMk_right p x
    have hb : HasFDerivAt (fun y : P × X n => (y,t))
        (ContinuousLinearMap.inl ℝ (P × X n) ℝ) (p,x) :=
      hasFDerivAt_prodMk_left (p,x) t
    exact hb.comp x hs
  have h := (((hV.differentiable (by simp) ((p,x),t)).hasFDerivAt).comp x hM).fderiv
  simpa only [splitFirst,EuclideanSpace.basisFun_apply,CalderonN.axis,Function.comp_def,L,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply] using
      congrArg (fun M : X n →L[ℝ] ℂ => M (axis i)) h

private theorem deriv_split_normal_joint {V : (P × X n) × ℝ → ℂ}
    (hV : ContDiff ℝ ∞ V) (p : P) (x : X n) (t : ℝ) :
    splitNormal (fun z : X n × ℝ => V ((p,z.1),z.2)) x t =
      fderiv ℝ V ((p,x),t) (0,1) := by
  unfold splitNormal
  have h := (((hV.differentiable (by simp) ((p,x),t)).hasFDerivAt).comp t
    (hasFDerivAt_prodMk_right (p,x) t)).hasDerivAt.deriv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using h

theorem jointSplitOperator_contDiffOn
    {O : Set ((P × X n) × ℝ)}
    {A : (P × X n) × ℝ → Matrix (I n) (I n) ℂ}
    {τ : (P × X n) × ℝ → ℂ} {c : (P × X n) × ℝ → I n → ℂ}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun q => A q i j) O) (hτ : ContDiffOn ℝ ∞ τ O)
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun q => c q i) O)
    {V : (P × X n) × ℝ → ℂ} (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (jointSplitOperator A τ c V) O := by
  let D (v : (P × X n) × ℝ) (q : (P × X n) × ℝ) := fderiv ℝ V q v
  have hD (v : (P × X n) × ℝ) : ContDiff ℝ ∞ (D v) :=
    (hV.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  let slice (p : P) := fun z : X n × ℝ => V ((p,z.1),z.2)
  have hT (q : (P × X n) × ℝ) (i : I n) :
      splitFirst (slice q.1.1) q.1.2 q.2 i = D ((0,axis i),0) q :=
    fderiv_split_tangent_joint hV _ _ _ i
  have hN (q : (P × X n) × ℝ) :
      splitNormal (slice q.1.1) q.1.2 q.2 = D (0,1) q :=
    deriv_split_normal_joint hV _ _ _
  have hTT (q : (P × X n) × ℝ) (i j : I n) :
      splitSecond (slice q.1.1) q.1.2 q.2 i j =
        fderiv ℝ (D ((0,axis j),0)) q ((0,axis i),0) := by
    unfold splitSecond
    change fderiv ℝ (fun y => splitFirst (slice q.1.1) y q.2 j) q.1.2 _ = _
    simp_rw [show ∀ y : X n, splitFirst (slice q.1.1) y q.2 j =
      D ((0,axis j),0) ((q.1.1,y),q.2) from fun y => hT ((q.1.1,y),q.2) j]
    exact fderiv_split_tangent_joint (hD ((0,axis j),0)) q.1.1 q.1.2 q.2 i
  have hNN (q : (P × X n) × ℝ) :
      splitNormalSecond (slice q.1.1) q.1.2 q.2 =
        fderiv ℝ (D (0,1)) q (0,1) := by
    unfold splitNormalSecond
    change deriv (fun t => splitNormal (slice q.1.1) q.1.2 t) q.2 = _
    simp_rw [show ∀ t : ℝ, splitNormal (slice q.1.1) q.1.2 t =
      D (0,1) (q.1,t) from fun t => hN (q.1,t)]
    exact deriv_split_normal_joint (hD (0,1)) q.1.1 q.1.2 q.2
  have hDD (v w : (P × X n) × ℝ) :
      ContDiff ℝ ∞ (fun q => fderiv ℝ (D v) q w) :=
    ((hD v).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  change ContDiffOn ℝ ∞ (fun q => complexSplitOperator (A q) (τ q) (c q)
    (slice q.1.1) q.1.2 q.2) O
  simp only [complexSplitOperator,hT,hN,hTT,hNN]
  exact (((hDD _ _).neg.contDiffOn.sub
    (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hA i j).mul (hDD _ _).contDiffOn)).add
      ((hτ.div_const 2).mul (hD _).contDiffOn)).sub
    (ContDiffOn.sum fun i _ => (hc i).mul (hD _).contDiffOn)

/-- Zero germs of the wave give zero germs of its differential residual,
including at points just outside the compact collar. -/
theorem jointSplitOperator_zero_outside_support
    {K : Set (X n × ℝ)} (hK : IsClosed K)
    {V : (P × X n) × ℝ → ℂ} (hSupp : ∀ p x, x ∉ K → V ((p,x.1),x.2) = 0)
    (A : (P × X n) × ℝ → Matrix (I n) (I n) ℂ)
    (τ : (P × X n) × ℝ → ℂ) (c : (P × X n) × ℝ → I n → ℂ)
    (p : P) {z : X n × ℝ} (hz : z ∉ K) :
    jointSplitOperator A τ c V ((p,z.1),z.2) = 0 := by
  let w (x : X n × ℝ) := V ((p,x.1),x.2)
  have hW : w =ᶠ[𝓝 z] fun _ => (0:ℂ) :=
    Filter.mem_of_superset (hK.isOpen_compl.mem_nhds hz) (hSupp p)
  have hN₀ : (fun t => w (z.1,t)) =ᶠ[𝓝 z.2] fun _ => (0:ℂ) :=
    hW.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  have hT₀ : (fun x => w (x,z.2)) =ᶠ[𝓝 z.1] fun _ => (0:ℂ) :=
    hW.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hN : splitNormal w z.1 z.2 = 0 := by
    unfold splitNormal
    rw [hN₀.deriv_eq]
    simp
  have hNN : splitNormalSecond w z.1 z.2 = 0 := by
    unfold splitNormalSecond
    rw [hN₀.deriv.deriv_eq]
    simp
  have hT (i : I n) : splitFirst w z.1 z.2 i = 0 := by
    unfold splitFirst
    rw [hT₀.fderiv_eq]
    simp
  have hTT (i j : I n) : splitSecond w z.1 z.2 i j = 0 := by
    unfold splitSecond
    have hE : (fun x => fderiv ℝ (fun y => w (y,z.2)) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᶠ[𝓝 z.1]
        fun _ => (0:ℂ) := by
      filter_upwards [hT₀.fderiv (𝕜 := ℝ)] with x hx
      rw [hx]
      simp
    rw [hE.fderiv_eq]
    simp
  change complexSplitOperator _ _ _ w z.1 z.2 = 0
  simp only [complexSplitOperator,hN,hNN,hT,hTT,mul_zero,neg_zero,add_zero,sub_zero,Finset.sum_const_zero]

end CalderonPatch.BoundaryLayer
