module

public import Proof.Manuscript.MovingTrace.CutTrialResidual
public import Proof.Manuscript.MovingTrace.ParametricExactResidualEnvelope
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Filter Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper

variable {n : ℕ}
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

/-- The controlled collar model is the actual forced equation of the
lifted wave, multiplied by the fixed signed exterior cutoff. -/
theorem exists_uniform_physical_residual_of_collar_model
    (v : ↥S) {W : Set (P × Z)} (hW : IsOpen W)
    (g a : P × Z → Mat (n+1))
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) W)
    (hPos : ∀ q ∈ W, (g q).PosDef)
    (ha : ∀ q ∈ W, ∀ i j, a q i j = divergenceCoeff (fun z => g (q.1,z)) q.2 i j)
    (w : ℝ → P × Z → ℂ) (hw : ∀ h, ContDiff ℝ ∞ (w h))
    (u : ℝ → (P × X n) × ℝ → ℂ) (hu : ∀ h, ContDiff ℝ ∞ (u h))
    (hTrial : ∀ h p x t, t < 1 →
      w h (p,polarCollar (angularPoint v) (x,t)) = u h ((p,x),t))
    {J : Set P} (hJ : IsCompact J)
    {K : Set (X n × ℝ)} (hK : IsCompact K) (hKe : ∀ q ∈ K, q.2 < 1)
    {O : Set ((P × X n) × ℝ)} (hO : IsOpen O)
    (hKO : ∀ p ∈ J, ∀ q ∈ K, ((p,q.1),q.2) ∈ O)
    (hOW : ∀ q ∈ O, (q.1.1,polarCollar (angularPoint v) (q.1.2,q.2)) ∈ W)
    (hDepth : ∀ q ∈ O, q.2 < 1)
    (hMix : ∀ q ∈ O, ∀ j : I n, pullbackMetric (fun z => g (q.1.1,z)) (signedSphericalCollar v)
      (signedLayerCoordinates (q.1.2,q.2)) 0 j.succ = 0)
    {h₀ : ℝ} (hh₀ : h₀ ≤ 1)
    (hSupp : ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ p z,
      z ∉ (stereographicPolarCollar v) '' K → cutTrialResidual a (w h) h (p,z) = 0)
    (N : ℕ) (weight : ℝ → ℝ) (hWeight : ∀ h : ℝ, 0 < h → h ≤ 1 → 0 ≤ weight h)
    (hSplit : let m (p : P) := pullbackMetric (fun z => g (p,z)) (signedSphericalCollar v)
      let A (q : (P × X n) × ℝ) := Matrix.of
        (fun i j => (collarTangential (m q.1.1) (q.1.2,q.2) i j : ℂ))
      let τ (q : (P × X n) × ℝ) := (collarNormalDrift (m q.1.1) (q.1.2,q.2) : ℂ)
      let c (q : (P × X n) × ℝ) (i : I n) := (collarTangentDrift (m q.1.1) (q.1.2,q.2) i : ℂ)
      SmoothCollarContribution {q | q.1.1 ∈ J ∧ (q.1.2,q.2) ∈ K}
        (fun h => jointSplitOperator A τ c (u h)) N weight) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ p : P, p ∈ J → ∀ z : Z, ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (cutTrialResidual a (w h) h) (p,z)‖ ≤ C * (h⁻¹^N * weight h) := by
  let e := stereographicPolarCollar v
  let m (p : P) := pullbackMetric (fun z => g (p,z)) (signedSphericalCollar v)
  let A (q : (P × X n) × ℝ) := Matrix.of
    (fun i j => (collarTangential (m q.1.1) (q.1.2,q.2) i j : ℂ))
  let τ (q : (P × X n) × ℝ) := (collarNormalDrift (m q.1.1) (q.1.2,q.2) : ℂ)
  let c (q : (P × X n) × ℝ) (i : I n) := (collarTangentDrift (m q.1.1) (q.1.2,q.2) i : ℂ)
  let z (q : (P × X n) × ℝ) := polarCollar (angularPoint v) (q.1.2,q.2)
  let f (h : ℝ) (q : (P × X n) × ℝ) : ℂ :=
    if q.2 < 1 then complexNegativeBallDivergence
      (fun x => a (q.1.1,x)) (fun x => w h (q.1.1,x)) (z q) else 0
  let μ (q : (P × X n) × ℝ) :=
    ((chartVolume (fun x => g (q.1.1,x)) (z q) *
      collarInverseRadial (m q.1.1) (q.1.2,q.2) : ℝ) : ℂ)
  let Γ : Set ((P × X n) × ℝ) := {q | q.1.1 ∈ J ∧ (q.1.2,q.2) ∈ K}
  have hΓ : IsCompact Γ := by
    let re : P × (X n × ℝ) → (P × X n) × ℝ := fun q => ((q.1,q.2.1),q.2.2)
    have hre : Continuous re := (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
    have hEq : Γ = re '' (J ×ˢ K) := by
      ext ⟨⟨p,x⟩,t⟩
      constructor
      · intro h
        exact ⟨(p,x,t),h,rfl⟩
      · rintro ⟨⟨p',x',t'⟩,hp,hEq⟩
        cases hEq
        exact hp
    rw [hEq]
    exact (hJ.prod hK).image hre
  have hΓO : Γ ⊆ O := fun q hq => hKO q.1.1 hq.1 (q.1.2,q.2) hq.2
  have hz : ContDiff ℝ ∞ z := ((contDiff_const.sub contDiff_snd).smul
    ((angularPoint_contDiff v).comp contDiff_fst.snd))
  have hzMap : ContDiff ℝ ∞ (fun q : (P × X n) × ℝ => (q.1.1,z q)) := contDiff_fst.fst.prodMk hz
  have hgZ (i j : I (n+1)) : ContDiffOn ℝ ∞ (fun q => g (q.1.1,z q) i j) O :=
    (hg i j).comp hzMap.contDiffOn hOW
  have hVol : ContDiffOn ℝ ∞
      (fun q => chartVolume (fun x => g (q.1.1,x)) (z q)) O :=
    (contDiffOn_det_of_entries hgZ).sqrt (fun q hq => (hPos _ (hOW q hq)).det_pos.ne')
  have hdF (i j : I (n+1)) : ContDiff ℝ ∞ (fun q : (P × X n) × ℝ =>
      coordinateJacobian (signedSphericalCollar v) (signedLayerCoordinates (q.1.2,q.2)) i j) :=
    (contDiff_coordinateJacobian_entry _ (signedSphericalCollar_contDiff v) i j).comp
      (signedLayerCoordinates.contDiff.comp (contDiff_fst.snd.prodMk contDiff_snd))
  have hm (i j : I (n+1)) :
      ContDiffOn ℝ ∞ (fun q => m q.1.1 (signedLayerCoordinates (q.1.2,q.2)) i j) O := by
    have hQ (q : (P × X n) × ℝ) : signedSphericalCollar v (signedLayerCoordinates (q.1.2,q.2)) = z q := by
      simp [signedSphericalCollar,z]
    simp only [m,pullbackMetric,hQ,Matrix.mul_apply,Matrix.transpose_apply]
    exact ContDiffOn.sum fun l _ => (ContDiffOn.sum fun k _ => (hdF k i).contDiffOn.mul (hgZ k l)).mul
      (hdF l j).contDiffOn
  have hmPos (q) (hq : q ∈ O) : (m q.1.1 (signedLayerCoordinates (q.1.2,q.2))).PosDef := by
    have hB := signedSphericalCollar_derivative_bijective v (signedLayerCoordinates (q.1.2,q.2))
      (by simpa only [signedLayerCoordinates.symm_apply_apply] using hDepth q hq)
    have hDet := coordinateJacobian_det_ne_zero hB
    have hEq : signedSphericalCollar v (signedLayerCoordinates (q.1.2,q.2)) = z q := by
      simp [signedSphericalCollar,z]
    change ((coordinateJacobian (signedSphericalCollar v) _)ᵀ * g (q.1.1,
      signedSphericalCollar v (signedLayerCoordinates (q.1.2,q.2))) *
      coordinateJacobian (signedSphericalCollar v) _).PosDef
    rw [hEq,← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (hPos _ (hOW q hq)).conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hDet)))
  have hRad : ContDiffOn ℝ ∞ (fun q => collarInverseRadial (m q.1.1) (q.1.2,q.2)) O :=
    contDiffOn_inv_entry_of_entries hm (fun q hq => (hmPos q hq).det_pos.ne') 0 0
  have hμ : ContDiffOn ℝ ∞ μ O := Complex.ofRealCLM.contDiff.comp_contDiffOn (hVol.mul hRad)
  have hFac := ParametricLayerCoefficients.SmoothCollarContribution.compact_unscaled hO hΓ hΓO hμ N
  have hMul : SmoothCollarContribution Γ
      (fun h q => μ q * jointSplitOperator A τ c (u h) q) N weight := by
    simpa only [one_mul] using hFac.mul (fun _ _ _ => zero_le_one) hWeight hSplit
  have hComp : SmoothCollarContribution Γ f N weight := by
    apply hMul.congr_on_open hO hΓO
    intro h hh hh₁ q hq
    let U := (Prod.mk q.1.1) ⁻¹' W
    have hU : IsOpen U := hW.preimage (continuous_const.prodMk continuous_id)
    have hG : SmoothMetric U (fun x => g (q.1.1,x)) :=
      ⟨fun i j => (hg i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hx => hx),
        fun x hx => hPos _ hx⟩
    let wave (p : X n × ℝ) := u h ((q.1.1,p.1),p.2)
    have hWave : ContDiff ℝ ∞ wave := (hu h).comp
      ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd)
    have hW' : ContDiff ℝ ∞ (fun z => w h (q.1.1,z)) := (hw h).comp (contDiff_const.prodMk contDiff_id)
    have hEw : EqOn ((fun z => w h (q.1.1,z)) ∘ polarCollar (angularPoint v)) wave {q | q.2 < 1} :=
      fun p hp => hTrial h q.1.1 p.1 p.2 hp
    simp only [f,ite_eq_left (hDepth q hq)]
    exact complexNegativeBallDivergence_eq_collarSplit hU hG (fun x hx => ha _ hx)
      v hW' hWave hEw q.1.2 q.2 (hDepth q hq) (hOW q hq) (hMix q hq)
  have hExact (h : ℝ) (hh : 0 < h) (hh₀ : h ≤ h₀) :
      collarLift e (fun (p : P × (X n × ℝ)) => residualCutIn (p.2.2/h) * f h ((p.1,p.2.1),p.2.2)) =
        cutTrialResidual a (w h) h := by
    funext q
    by_cases hq : q.2 ∈ e.target
    · let b := e.symm q.2
      have hb : b.2 < 1 := e.map_target hq
      have hDepthEq : b.2 = 1-‖q.2‖ := rfl
      have hPos : z ((q.1,b.1),b.2) = q.2 := e.right_inv hq
      rw [collarLift,ite_eq_left hq]
      change residualCutIn (b.2/h) * f h ((q.1,b.1),b.2) = cutTrialResidual a (w h) h q
      change residualCutIn (b.2/h) * (if b.2 < 1 then complexNegativeBallDivergence
        (fun x => a (q.1,x)) (fun x => w h (q.1,x)) (z ((q.1,b.1),b.2)) else 0) = _
      rw [ite_eq_left hb,hPos,hDepthEq]
      rfl
    · rw [collarLift,ite_eq_right hq,hSupp h hh hh₀ q.1 q.2]
      rintro ⟨p,hp,he⟩
      exact hq (he ▸ e.map_source (hKe p hp))
  have hLiftSupp (h : ℝ) (hh : 0 < h) (hhh : h ≤ h₀) (p : P) (q : X n × ℝ) (hq : q ∉ K) :
      residualCutIn (q.2/h) * f h ((p,q.1),q.2) = 0 := by
    by_cases ht : q.2 < 1
    · have htarg := e.map_source (show q ∈ e.source from ht)
      have hN : ‖z ((p,q.1),q.2)‖ = 1-q.2 := by
        change ‖(1-q.2) • angularPoint v q.1‖ = _
        rw [norm_smul,Real.norm_of_nonneg (sub_nonneg.mpr ht.le),angularPoint_norm,mul_one]
      have hDepthEq : 1-‖z ((p,q.1),q.2)‖ = q.2 := by rw [hN]; ring
      have hOut : z ((p,q.1),q.2) ∉ e '' K := by
        rintro ⟨q',hq',heq⟩
        apply hq
        exact ((e.injOn (hKe q' hq') (show q ∈ e.source from ht)
          (show e q' = e q from heq)) ▸ hq')
      simp only [f,ite_eq_left ht]
      rw [← hSupp h hh hhh p _ hOut,cutTrialResidual,hDepthEq]
    · simp [f,ht]
  obtain ⟨C,hC,hBound⟩ := exists_uniform_jet_bound_lifted_residual e (polarReadout_contDiffOn v)
    hJ hK hKe f hh₀ hLiftSupp N weight hWeight hComp
  exact ⟨C,hC,fun h hh hhh p hp z j hj => hExact h hh hhh ▸ hBound h hh hhh p hp z j hj⟩

end CalderonPaper
