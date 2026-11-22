module

public import Proof.CalderonN.NormalJointParameterJets
public import Proof.CalderonN.HigherFlowJetBounds

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem NormalCoordinates.parameterJetField_initial_norm_le_one {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (n : ℕ) (hn : 1 ≤ n)
    {y : (X dim)} (hy : y ∈ Y) (hR : ContinuousAt R y) (v : (X dim))
    (hv : metricPair g y v v < (R y)^2) :
    ‖parameterJetField n (normalJointPhase expMap) ((y,v),0)‖ ≤ 1 := by
  have hEq : (fun p : (X dim) × (X dim) => normalJointPhase expMap (p,0)) =ᶠ[𝓝 (y,v)] (fun p => p) := by
    filter_upwards [hN.eventually_joint_disk hY hΩ hg hy hR v hv] with p hp
    exact (hN.jointPhase_eq_phase hp.1 p.2 0
      (by simpa only [zero_smul] using zero_mem_disk g p.1 (R p.1))).trans
      (hN.phase_zero hp.1 p.2 hp.2)
  rw [hN.parameterJetField_eq_slice n hy v 0
    (by simpa only [zero_smul] using zero_mem_disk g y (R y)),
    (hEq.iteratedFDeriv ℝ n).eq_of_nhds]
  cases n with
  | zero => omega
  | succ n =>
    rw [← norm_iteratedFDeriv_fderiv]
    have hD : fderiv ℝ (fun p : (X dim) × (X dim) => p) =
        fun _ => ContinuousLinearMap.id ℝ ((X dim) × (X dim)) := funext fun _ => fderiv_id
    rw [hD]
    cases n with
    | zero => simpa only [norm_iteratedFDeriv_zero] using
        (ContinuousLinearMap.norm_id_le (𝕜:=ℝ) (E:=((X dim) × (X dim))))
    | succ n => simp [iteratedFDeriv_succ_const]

/-- A conditional all-order endpoint producer for the actual normal map.
    Its only quantitative premise is a uniform finite spray-jet bound. -/
theorem NormalCoordinates.joint_higher_jet_bound_of_spray_jets {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) (hK : 0 < K) {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (N : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (hSpray : ∀ x ∈ Ω, ∀ w : (X dim), ‖w‖ ≤ K → ∀ j, 1 ≤ j → j ≤ N →
      ‖iteratedFDeriv ℝ j (coordinateGeodesicSpray g) (x,w)‖ ≤ S)
    {y : (X dim)} (hy : y ∈ Y) (hR : ContinuousAt R y) (v : (X dim))
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖iteratedFDeriv ℝ n (fun p => normalJointPhase expMap (p,t)) (y,v)‖ ≤
      higherFlowJetBudget S N := by
  let phi : ℝ → ((X dim) × (X dim)) → (X dim) × (X dim) := fun t p => normalJointPhase expMap (p,t)
  let J := fun n t => parameterJetField n (normalJointPhase expMap) ((y,v),t)
  have hSmooth (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ (phi s) (y,v) :=
    (hN.contDiffAt_jointPhase hy v s (smul_mem_disk_of_mem g y v (R y) s hv.le hs)).comp
      (y,v) (contDiffAt_id.prodMk contDiffAt_const)
  have hGeom (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      (phi s (y,v)).1 ∈ Ω ∧ ‖(phi s (y,v)).2‖ ≤ K := by
    refine ⟨hN.path_image hy v hv.le hs,?_⟩
    change ‖(normalJointPhase expMap ((y,v),s)).2‖ ≤ K
    rw [hN.jointPhase_eq_phase hy v s (smul_mem_disk_of_mem g y v (R y) s hv.le hs),hN.phase_eq hy v hv.le hs]
    exact (hN.geodesic_speed_le hΩ hg hK hy v hv.le hs).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hK.le)
  have hJS (j : ℕ) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : J j s = iteratedFDeriv ℝ j (phi s) (y,v) :=
    hN.parameterJetField_eq_slice j hy v s (smul_mem_disk_of_mem g y v (R y) s hv.le hs)
  rw [← hJS n t ht]
  exact flow_jets_le_higherFlowJetBudget phi (coordinateGeodesicSpray g) (y,v) J S hS hSmooth
    (fun s hs => hg.contDiffAt_coordinateGeodesicSpray hΩ hK _ (hGeom s hs).1) hJS
    (fun j _ s hs => hN.hasDerivAt_parameterJetField hY hΩ hg j hy hR v hv hs)
    (fun j hj => hN.parameterJetField_initial_norm_le_one hY hΩ hg j hj hy hR v hv)
    N (fun s hs j hj hjN => hSpray _ (hGeom s hs).1 _ (hGeom s hs).2 j hj hjN)
    n hn hnN t ht

theorem NormalCoordinates.expMap_higher_jet_bound_of_spray_jets {Y Ω : Set (X dim)}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) (hK : 0 < K) {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) (N : ℕ) (S : ℝ) (hS : 0 ≤ S)
    (hSpray : ∀ x ∈ Ω, ∀ w : (X dim), ‖w‖ ≤ K → ∀ j, 1 ≤ j → j ≤ N →
      ‖iteratedFDeriv ℝ j (coordinateGeodesicSpray g) (x,w)‖ ≤ S)
    {y : (X dim)} (hy : y ∈ Y) (hR : ContinuousAt R y) (v : (X dim))
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n expMap (y,v)‖ ≤ higherFlowJetBudget S N := by
  let F : ((X dim) × (X dim)) → (X dim) × (X dim) := fun p => normalJointPhase expMap (p,1)
  have hvd : v ∈ disk g y (R y) := hv.le
  have hF : ContDiffAt ℝ ∞ F (y,v) :=
    (hN.contDiffAt_jointPhase hy v 1 (by simpa only [one_smul] using hvd)).comp
      (y,v) (contDiffAt_id.prodMk contDiffAt_const)
  let L : ((X dim) × (X dim)) →L[ℝ] (X dim) := ContinuousLinearMap.fst ℝ (X dim) (X dim)
  have hEq : L ∘ F = expMap := by funext p; simp only [Function.comp_apply,L,F,normalJointPhase,one_smul];rfl
  have hBound := hN.joint_higher_jet_bound_of_spray_jets hY hΩ hg hK N S hS hSpray
    hy hR v hv hv1 n hn hnN (t:=1) (by simp)
  rw [← hEq,L.iteratedFDeriv_comp_left hF (i:=n) (by simp)]
  apply ContinuousMultilinearMap.opNorm_le_bound (zero_le_one.trans (one_le_higherFlowJetBudget S hS N))
  intro m
  change ‖(iteratedFDeriv ℝ n F (y,v) m).1‖ ≤ _
  exact (norm_fst_le _).trans (((iteratedFDeriv ℝ n F (y,v)).le_opNorm m).trans
    (mul_le_mul_of_nonneg_right hBound (Finset.prod_nonneg (fun _ _ => norm_nonneg _))))

end CalderonN
