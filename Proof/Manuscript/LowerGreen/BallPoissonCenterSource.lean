module

public import Proof.Manuscript.LowerGreen.BallCutoffDuality
public import Proof.Manuscript.LowerGreen.BallCutoffWeakForward
public import Proof.Manuscript.LowerGreen.ClosedBallOperatorLift

import Mathlib.Tactic

public section

noncomputable section

open Set Metric MeasureTheory Filter CalderonN CalderonN.BallDirichlet TauCeti
open scoped ContDiff ENNReal InnerProductSpace Topology Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

namespace SupportedBallFamily

variable (F : SupportedBallFamily P n) {p : P}

set_option maxHeartbeats 1400000 in
theorem inner_forwardL_backwardL_on_closed (hp : p ∈ F.V)
    (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (hSupp : tsupport χ.1 ⊆ ball (0 : X n) (1/2))
    (s t : ℕ) (v : ClosedBallSobolev n t) (u : SmoothData n) :
    ⟪Wkp.value t v.1,Wkp.value (s+2) (F.forwardL s χ hχ p (smoothBallSobolev (s+1) u))⟫_ℝ =
    ⟪Wkp.value (t+1) (F.backwardL t χ hχ p v.1),Wkp.value (s+1) (smoothBallSobolev (s+1) u)⟫_ℝ := by
  refine (denseRange_denseSmoothBallSobolev n t).induction_on v ?_ ?_
  · apply isClosed_eq
    · exact ((Wkp.valueL t).continuous.comp continuous_subtype_val).inner continuous_const
    · exact ((Wkp.valueL (t+1)).continuous.comp ((F.backwardL t χ hχ p).continuous.comp
        continuous_subtype_val)).inner continuous_const
  · intro f
    exact F.inner_forwardL_backwardL_on_smooth hp χ hχ hSupp s t ⟨f.1,f.2⟩ u

theorem backwardChainL_mem_closed (hp : p ∈ F.V)
    (χ : ℕ → SmoothData n) (hc : ∀ j, HasCompactSupport (χ j).1)
    (j m : ℕ) (v : ClosedBallSobolev n 0) :
    F.backwardChainL χ hc p j m v.1 ∈ closedBallSobolev n m := by
  induction m with
  | zero => exact v.2
  | succ m ih =>
    change F.backwardL m (χ (j+m)) (hc (j+m)) p
      (F.backwardChainL χ hc p j m v.1) ∈ closedBallSobolev n (m+1)
    exact maps_closedBallSobolev_of_smooth _ (fun f => by
      obtain ⟨g,hg⟩ := F.backwardL_smooth_representative hp (χ (j+m)) (hc (j+m)) f
      exact ⟨g,hg m⟩) ⟨_,ih⟩

set_option maxHeartbeats 2400000 in
/-- A smooth parameter-dependent volume source of any prescribed Sobolev
order represents center evaluation on the harmonic subspace. -/
theorem exists_ballPoissonCenterSource (l : ℕ) :
    ∃ b : P → ClosedBallSobolev n l, ContDiffOn ℝ ∞ b F.V ∧
      ∀ p ∈ F.V, ∀ u : SmoothData n,
        EqOn (negativeBallDivergence (fun z => F.a (p,z)) u.1) 0 (ball (0 : X n) 1) →
        ⟪Wkp.value l (b p).1,smoothBallSobolev 0 u⟫_ℝ = u.1 0 := by
  obtain ⟨χ,hc,hSupp,hOne,hNest⟩ := exists_nestedBallCutoffs (n := n)
  obtain ⟨A,hA⟩ := exists_ballCenterEvalL (n := n) (s := n+1) le_rfl
  let T (p : P) : BallSobolev n 0 →L[ℝ] BallSobolev n (n+1) :=
    (F.forwardChainL χ hc p 0 n).comp (F.weakForwardL (χ n) (hc n) p)
  have hT : ContDiffOn ℝ ∞ T F.V :=
    (F.contDiffOn_forwardChainL χ hc 0 n).clm_comp (F.contDiffOn_weakForwardL (χ n) (hc n))
  let b₀ (p : P) := closedBallCenterRiesz (n+1) A (T p)
  have hb₀ : ContDiffOn ℝ ∞ b₀ F.V := contDiffOn_closedBallCenterRiesz A hT
  have hb₀' : ContDiffOn ℝ ∞ (fun p => (b₀ p).1) F.V :=
    ((closedBallSobolev n 0).toSubmodule.subtypeL).contDiff.comp_contDiffOn hb₀
  let C (k : ℕ) (p : P) : BallSobolev n k :=
    F.backwardChainL χ hc p (n+1) k (b₀ p).1
  have hC (k : ℕ) : ContDiffOn ℝ ∞ (C k) F.V :=
    (F.contDiffOn_backwardChainL χ hc (n+1) k).clm_apply hb₀'
  have hm (k : ℕ) (p : P) (hp : p ∈ F.V) : C k p ∈ closedBallSobolev n k :=
    F.backwardChainL_mem_closed hp χ hc (n+1) k (b₀ p)
  obtain ⟨b,hb,he⟩ := exists_smooth_closedBall_lift F.openV (hC l) (hm l)
  refine ⟨b,hb,fun p hp u hu => ?_⟩
  have hLocal (v : SmoothData n) (hv : ∀ z ∈ tsupport (χ n).1, v.1 =ᶠ[𝓝 z] u.1) :
      ⟪Wkp.value 0 (C 0 p),smoothBallSobolev 0 v⟫_ℝ = u.1 0 := by
    rw [Wkp.value_zero]
    change ⟪(b₀ p).1,(denseSmoothBallSobolev n 0 ⟨v.1,v.2⟩).1⟫_ℝ = _
    rw [closedBallCenterRiesz_inner]
    change A (F.forwardChainL χ hc p 0 n
      (F.weakForwardL (χ n) (hc n) p (smoothBallSobolev 0 v))) = _
    rw [F.weakForwardL_apply_localized hp (χ n) (hc n) (hSupp n) u v hu hv]
    have hChain := F.forwardChainL_cutoff hp χ hc hSupp hNest u hu 0 n
    simp only [zero_add] at hChain
    rw [hChain]
    let w := cutoffData (χ 0) u
    change A (smoothBallSobolevLinear n (n+1) ⟨w.1,w.2⟩) = _
    rw [hA]
    change (χ 0).1 0 * u.1 0 = u.1 0
    rw [hOne,one_mul]
  have hStep (k : ℕ) (v : SmoothData n)
      (hv : ∀ z ∈ tsupport (χ (n+1+k)).1, v.1 =ᶠ[𝓝 z] u.1) :
      ⟪Wkp.value (k+1) (C (k+1) p),smoothBallSobolev 0 v⟫_ℝ =
      ⟪Wkp.value k (C k p),smoothBallSobolev 0 (cutoffData (χ (n+1+k)) u)⟫_ℝ := by
    have h := F.inner_forwardL_backwardL_on_closed hp (χ (n+1+k)) (hc (n+1+k))
      (hSupp (n+1+k)) 0 k ⟨C k p,hm k p hp⟩ v
    have hF := F.forwardL_apply_localized hp (χ (n+1+k)) (hc (n+1+k)) (hSupp (n+1+k)) u v hu hv 0
    change ⟪Wkp.value k (C k p),Wkp.value 2 (F.forwardL 0 (χ (n+1+k)) (hc (n+1+k)) p
      (smoothBallSobolev 1 v))⟫_ℝ =
      ⟪Wkp.value (k+1) (C (k+1) p),Wkp.value 1 (smoothBallSobolev 1 v)⟫_ℝ at h
    rw [hF] at h
    have hLower (s : ℕ) (w : SmoothData n) : Wkp.value s (smoothBallSobolev s w) =
        smoothBallSobolev 0 w := by
      apply Lp.ext
      exact (value_smoothBallSobolev_ae s w).trans
        ((Wkp.value_zero (smoothBallSobolev 0 w)) ▸ (value_smoothBallSobolev_ae 0 w)).symm
    rw [hLower 2 _,hLower 1 v] at h
    exact h.symm
  have hCut (k : ℕ) :
      ⟪Wkp.value k (C k p),smoothBallSobolev 0 (cutoffData (χ (n+1+k)) u)⟫_ℝ = u.1 0 := by
    induction k with
    | zero =>
      exact hLocal _ (fun z hz => cutoffData_germ _ _ (hNest n z hz))
    | succ k ih =>
      rw [show n+1+(k+1) = n+1+k+1 by omega]
      rw [hStep k _ (fun z hz => cutoffData_germ _ _ (hNest (n+1+k) z hz))]
      exact ih
  rw [he p hp]
  cases l with
  | zero => exact hLocal u (fun _ _ => EventuallyEq.rfl)
  | succ k =>
    rw [hStep k u (fun _ _ => EventuallyEq.rfl)]
    exact hCut k

end SupportedBallFamily

end CalderonPaper.LowerGreen

end
