import Proof.LocalMixedParameterJetCalculus
import Proof.NormalJointGeodesicPhase
import Proof.FourthBilinearVelocityBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter
open scoped ContDiff Topology
open OAI.AnisotropicCalderon.ConnectionError
namespace ShrinkingSpheres

/-- The normal-coordinate smoothness hypothesis supplies an actual open
    smooth domain for the joint phase, not merely pointwise smoothness. -/
theorem NormalCoordinates.exists_open_smooth_jointPhase {Y Ω : Set X}
    {g : MetricField} {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) :
    ∃ U : Set ((X × X) × ℝ), IsOpen U ∧ ContDiffOn ℝ ∞ (normalJointPhase expMap) U ∧
      ∀ y ∈ Y, ∀ v t, t • v ∈ disk g y (R y) → ((y,v),t) ∈ U := by
  obtain ⟨V,hV,hTube,hReg⟩ := hN.1
  let input : (X × X) × ℝ → X × X := fun p => (p.1.1,p.2 • p.1.2)
  have hi : ContDiff ℝ ∞ input :=
    contDiff_fst.fst.prodMk (contDiff_snd.smul contDiff_fst.snd)
  have hv : ContDiff ℝ ∞ (fun p : (X × X) × ℝ => ((0:X),p.1.2)) :=
    contDiff_const.prodMk contDiff_fst.snd
  refine ⟨input ⁻¹' V,hV.preimage hi.continuous,?_,?_⟩
  · exact (hReg.comp hi.contDiffOn (fun _ h => h)).prodMk
      (((hReg.fderiv_of_isOpen (m:=∞) hV (by simp)).comp hi.contDiffOn
        (fun _ h => h)).clm_apply hv.contDiffOn)
  · intro y hy v t ht
    exact hTube ⟨hy,ht⟩

theorem NormalCoordinates.parameterJetField_eq_slice {Y Ω : Set X}
    {g : MetricField} {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (n : ℕ) {y : X} (hy : y ∈ Y)
    (v : X) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    parameterJetField n (normalJointPhase expMap) ((y,v),t) =
      iteratedFDeriv ℝ n (fun p => normalJointPhase expMap (p,t)) (y,v) := by
  obtain ⟨U,hU,hF,hMem⟩ := hN.exists_open_smooth_jointPhase
  exact parameterJetField_eq_iteratedFDeriv_of_open n _ hU hF (y,v) t (hMem y hy v t hv)

/-- Every finite parameter jet satisfies the differentiated spray equation.
    The right side remains the unexpanded derivative of a composition so
    that Faa di Bruno can isolate its highest jet linearly. -/
theorem NormalCoordinates.hasDerivAt_parameterJetField {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (n : ℕ) {y : X} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : X) (hv : metricPair g y v v < (R y)^2)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => parameterJetField n (normalJointPhase expMap) ((y,v),s))
      (iteratedFDeriv ℝ n ((coordinateGeodesicSpray g) ∘
        (fun p => normalJointPhase expMap (p,t))) (y,v)) t := by
  obtain ⟨U,hU,hF,hMem⟩ := hN.exists_open_smooth_jointPhase
  have hODE : (fun p => radialFirstDerivative (normalJointPhase expMap) (p,t)) =ᶠ[𝓝 (y,v)]
      ((coordinateGeodesicSpray g) ∘ (fun p => normalJointPhase expMap (p,t))) := by
    filter_upwards [hN.eventually_joint_disk hY hΩ hg hy hR v hv] with p hp
    have hPx := hN.contDiffAt_jointPhase hp.1 p.2 t
      (smul_mem_disk_of_mem g p.1 p.2 (R p.1) t hp.2 ht)
    exact (hasDerivAt_time_slice (normalJointPhase expMap) p t
      (hPx.differentiableAt (by simp))).unique (hN.hasDerivAt_jointPhase hp.1 p.2 hp.2 ht)
  have hd := hasDerivAt_parameterJetField_of_open n (normalJointPhase expMap) hU hF
    (y,v) t (hMem y hy v t (smul_mem_disk_of_mem g y v (R y) t hv.le ht))
  rw [(hODE.iteratedFDeriv ℝ n).eq_of_nhds] at hd
  exact hd

theorem NormalCoordinates.parameterJetField_initial_higher {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (n : ℕ) (hn : 2 ≤ n)
    {y : X} (hy : y ∈ Y) (hR : ContinuousAt R y) (v : X)
    (hv : metricPair g y v v < (R y)^2) :
    parameterJetField n (normalJointPhase expMap) ((y,v),0) = 0 := by
  have hEq : (fun p : X × X => normalJointPhase expMap (p,0)) =ᶠ[𝓝 (y,v)] (fun p => p) := by
    filter_upwards [hN.eventually_joint_disk hY hΩ hg hy hR v hv] with p hp
    exact (hN.jointPhase_eq_phase hp.1 p.2 0
      (by simpa only [zero_smul] using zero_mem_disk g p.1 (R p.1))).trans
      (hN.phase_zero hp.1 p.2 hp.2)
  rw [hN.parameterJetField_eq_slice n hy v 0
    (by simpa only [zero_smul] using zero_mem_disk g y (R y)),
    (hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
  apply norm_eq_zero.mp
  have hnEq : n = k+2 := by omega
  rw [hnEq]
  exact norm_iteratedFDeriv_linear_higher (ContinuousLinearMap.id ℝ (X × X)) (y,v) k

end ShrinkingSpheres
