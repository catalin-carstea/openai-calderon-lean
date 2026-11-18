import Proof.AffineRescaledJetBounds
import Proof.NormalFrameRelativeGeometry
import Proof.OperatorFamilyJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def relativeFrameProjectionL : NormalFrameRelativeParameter →L[ℝ] (X →L[ℝ] X) :=
  (ContinuousLinearMap.snd ℝ X (X →L[ℝ] X)).comp
    (ContinuousLinearMap.fst ℝ (X × (X →L[ℝ] X)) ℝ)

def relativeRadiusProjectionL : NormalFrameRelativeParameter →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ (X × (X →L[ℝ] X)) ℝ

lemma norm_relativeFrameProjectionL_le_one : ‖relativeFrameProjectionL‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  exact (norm_snd_le p.1).trans (by simpa only [one_mul] using norm_fst_le p)

lemma norm_relativeRadiusProjectionL_le_one : ‖relativeRadiusProjectionL‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖p.2‖ ≤ 1*‖p‖
  simpa only [one_mul] using norm_snd_le p

/-- The horizontal lift expressed through connection and logarithmic-radius
    covector families. These can be rescaled BEFORE estimating derivatives. -/
def relativeHorizontalFieldOfFamilies
    (G : NormalFrameRelativeParameter → X →L[ℝ] X →L[ℝ] X)
    (l : NormalFrameRelativeParameter → X →L[ℝ] ℝ) (a : X)
    (p : NormalFrameRelativeParameter) : NormalFrameRelativeParameter :=
  ((a,-((G p a).comp (relativeFrameProjectionL p))),
    (1+relativeRadiusProjectionL p)*(l p a))

theorem contDiffAt_relativeHorizontalFieldOfFamilies
    (G : NormalFrameRelativeParameter → X →L[ℝ] X →L[ℝ] X)
    (l : NormalFrameRelativeParameter → X →L[ℝ] ℝ) (a : X) (p : NormalFrameRelativeParameter)
    (hG : ContDiffAt ℝ ∞ G p) (hl : ContDiffAt ℝ ∞ l p) :
    ContDiffAt ℝ ∞ (relativeHorizontalFieldOfFamilies G l a) p :=
  (contDiffAt_const.prodMk (((hG.clm_apply contDiffAt_const).clm_comp
    relativeFrameProjectionL.contDiff.contDiffAt).neg)).prodMk
      ((contDiffAt_const.add relativeRadiusProjectionL.contDiff.contDiffAt).mul
        (hl.clm_apply contDiffAt_const))

/-- Uniform finite lift jets involve only the metric connection, log-radius
    covector and frame VALUES. No frame-field derivatives occur. -/
theorem norm_iteratedFDeriv_relativeHorizontalFieldOfFamilies_le
    (G : NormalFrameRelativeParameter → X →L[ℝ] X →L[ℝ] X)
    (l : NormalFrameRelativeParameter → X →L[ℝ] ℝ) (a y : X) (L : X →L[ℝ] X)
    (hG : ContDiffAt ℝ ∞ G ((y,L),0)) (hl : ContDiffAt ℝ ∞ l ((y,L),0))
    (N : ℕ) (CG Cl K : ℝ) (hCG : 0 ≤ CG) (hCl : 0 ≤ Cl) (hK : 1 ≤ K) (hL : ‖L‖ ≤ K)
    (hGJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n G ((y,L),0)‖ ≤ CG)
    (hlJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n l ((y,L),0)‖ ≤ Cl)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (relativeHorizontalFieldOfFamilies G l a) ((y,L),0)‖ ≤
      (1+2^N*(CG*K+Cl))*‖a‖ := by
  let p0 : NormalFrameRelativeParameter := ((y,L),0)
  let Ga := fun p => G p a
  let la := fun p => l p a
  let s := fun p => 1+relativeRadiusProjectionL p
  let F := fun p => (Ga p).comp (relativeFrameProjectionL p)
  let R := fun p => s p*la p
  have hGa : ContDiffAt ℝ ∞ Ga p0 := hG.clm_apply contDiffAt_const
  have hla : ContDiffAt ℝ ∞ la p0 := hl.clm_apply contDiffAt_const
  have hs : ContDiffAt ℝ ∞ s p0 := contDiffAt_const.add relativeRadiusProjectionL.contDiff.contDiffAt
  have hF : ContDiffAt ℝ ∞ F p0 := hGa.clm_comp relativeFrameProjectionL.contDiff.contDiffAt
  have hR : ContDiffAt ℝ ∞ R p0 := hs.mul hla
  have hGaJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j Ga p0‖ ≤ CG*‖a‖ :=
    (norm_iteratedFDeriv_clm_apply_const (c:=a) hG (n:=j) (by simp)).trans
      ((mul_le_mul_of_nonneg_left (hGJets j hj) (norm_nonneg a)).trans_eq (by ring))
  have hlaJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j la p0‖ ≤ Cl*‖a‖ :=
    (norm_iteratedFDeriv_clm_apply_const (c:=a) hl (n:=j) (by simp)).trans
      ((mul_le_mul_of_nonneg_left (hlJets j hj) (norm_nonneg a)).trans_eq (by ring))
  have hFrameJets (j : ℕ) (_hj : j ≤ N) : ‖iteratedFDeriv ℝ j relativeFrameProjectionL p0‖ ≤ K := by
    by_cases hj0 : j=0
    · subst j
      rw [norm_iteratedFDeriv_zero]
      change ‖L‖ ≤ K
      exact hL
    · exact (norm_iteratedFDeriv_clm_le_one relativeFrameProjectionL norm_relativeFrameProjectionL_le_one p0 j (by omega)).trans hK
  have hsJets (j : ℕ) (_hj : j ≤ N) : ‖iteratedFDeriv ℝ j s p0‖ ≤ 1 := by
    by_cases hj0 : j=0
    · subst j
      norm_num [s,p0,relativeRadiusProjectionL]
    · rw [norm_iteratedFDeriv_affine_clm_positive relativeRadiusProjectionL 1 p0 j (by omega)]
      split_ifs
      · exact norm_relativeRadiusProjectionL_le_one
      · norm_num
  have hFJets : ‖iteratedFDeriv ℝ n F p0‖ ≤ (2^N*CG*K)*‖a‖ :=
    (norm_iteratedFDeriv_operator_comp_common_bound Ga relativeFrameProjectionL p0 hGa
      relativeFrameProjectionL.contDiff.contDiffAt N (CG*‖a‖) K (by positivity) (zero_le_one.trans hK)
      hGaJets hFrameJets n hn).trans_eq (by ring)
  have hRJets : ‖iteratedFDeriv ℝ n R p0‖ ≤ (2^N*Cl)*‖a‖ := by
    have hh := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.lsmul ℝ ℝ)
      s la p0 hs hla N 1 (Cl*‖a‖) zero_le_one (by positivity) hsJets hlaJets n hn
    exact hh.trans (by
      calc
        _ = ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖*((2^N*Cl)*‖a‖) := by ring
        _ ≤ 1*((2^N*Cl)*‖a‖) := mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le (by positivity)
        _ = _ := one_mul _)
  have hWhole : ‖iteratedFDeriv ℝ n (relativeHorizontalFieldOfFamilies G l a) p0‖ =
      max (max ‖iteratedFDeriv ℝ n (fun _ : NormalFrameRelativeParameter => a) p0‖
        ‖iteratedFDeriv ℝ n (fun p => -F p) p0‖) ‖iteratedFDeriv ℝ n R p0‖ := by
    change ‖iteratedFDeriv ℝ n (fun p => ((a,-F p),R p)) p0‖ = _
    rw [iteratedFDeriv_prodMk (contDiffAt_const.prodMk hF.neg) hR (i:=n) (by simp),
      ContinuousMultilinearMap.opNorm_prod,iteratedFDeriv_prodMk contDiffAt_const hF.neg (i:=n) (by simp),
      ContinuousMultilinearMap.opNorm_prod]
  rw [hWhole,norm_iteratedFDeriv_neg_at F p0 hF n]
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine max_le (max_le ?_ ?_) ?_
  · exact (norm_iteratedFDeriv_const_le a p0 n).trans (by nlinarith [mul_nonneg (show 0 ≤ (2:ℝ)^N*(CG*K+Cl) by positivity) (norm_nonneg a)])
  · exact hFJets.trans (mul_le_mul_of_nonneg_right (by nlinarith [show 0 ≤ (2:ℝ)^N*Cl by positivity]) (norm_nonneg a))
  · exact hRJets.trans (mul_le_mul_of_nonneg_right (by nlinarith [show 0 ≤ (2:ℝ)^N*CG*K by positivity]) (norm_nonneg a))

end ShrinkingSpheres
