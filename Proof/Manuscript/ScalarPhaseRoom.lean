module

public import Proof.Manuscript.ScalarCollarResidual
public import Proof.CalderonN.PhaseRooms

import Proof.CalderonN.PhaseRoomInterpolation
import Mathlib.Tactic

public section

noncomputable section
open Set Metric Filter CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

open Elliptic Elliptic.PhaseCoordinates

set_option maxHeartbeats 2200000 in
/-- In a fixed reference factor, the two asymmetric collars yield the
same interpolation exponent for every sufficiently small smooth scalar
perturbation. The rooms and constants come from the reference only. -/
theorem exists_reference_scalar_phaseRoom_interpolation
    {L₀ : ScalarElliptic n} (hL₀ : L₀.SmoothOn univ)
    {θ : X n → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : X n) (h₀ : θ p = 0)
    (hs : StrictMetricWeightAt L₀.metric θ p) :
    ∃ E : OpenPartialHomeomorph (X n) (ℝ × (fderiv ℝ θ p).ker), p ∈ E.source ∧
      (∀ x, E x = (θ x, (fderiv ℝ θ p).ker.orthogonalProjectionOnto (x-p))) ∧
      ∃ a k : ℝ, 0 < a ∧ 0 < k ∧
        Icc (-a) a ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) a ⊆ E.target ∧
        ∀ κ l ε R : ℝ, 0 < κ → κ ≤ k → 0 < ε → 4*ε < l → 0 < R →
          l+4*ε ≤ a → R ≤ a → κ*(l+4*ε) < 1/4 → 4*ε < κ*l^2 →
          let D := E.symm '' roomD l ε R
          let S := E.symm '' (roomStop l ε R ∪ roomSlat l ε R)
          let O := E.symm '' roomO l ε R
          IsOpen D ∧ S ⊆ D ∧ O ⊆ D ∧
            ∃ A γ : ℝ, 0 < A ∧ 1/2 < γ ∧ γ < 1 ∧
            ∀ L : ℝ → ScalarElliptic n, SmoothFamilyOn L univ → L 0 = L₀ →
              ∀ᶠ t in 𝓝 (0 : ℝ), (L t).Interpolates D S O A γ := by
  have hell : fderiv ℝ θ p ≠ 0 := fun h => hs.1 (funext fun i => by simp [coordDeriv,h])
  obtain ⟨E,hEp,hE,b₀,hb₀,hBig₀,hcut⟩ := exists_room_cutoff hθ p h₀ hell
  obtain ⟨r,C,τ₀,hr,hC,hτ₀,hCar⟩ := exists_reference_concave_scalarCarleman hL₀ hθ p hs
  obtain ⟨hp0,h0t⟩ := chart_symm_zero E hE (map_zero _) h₀ hEp
  obtain ⟨d,hd,hbox⟩ := exists_box_image_subset_ball E hp0 h0t hr
  let a := min b₀ (d/2)
  have ha : 0 < a := lt_min hb₀ (half_pos hd)
  have haa : a ≤ b₀ := min_le_left _ _
  have hBig : Icc (-a) a ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) a ⊆ E.target :=
    (Set.prod_mono (Icc_subset_Icc (neg_le_neg haa) haa) (closedBall_subset_closedBall haa)).trans hBig₀
  have hball := hbox a ((min_le_right _ _).trans_lt (half_lt_self hd)) hBig
  refine ⟨E,hEp,hE,a,r,ha,hr,hBig,fun κ l ε R hκ hκr hε hεl hR hl haR hκl hε4 => ?_⟩
  let D := E.symm '' roomD l ε R
  let S := E.symm '' (roomStop l ε R ∪ roomSlat l ε R)
  let O := E.symm '' roomO l ε R
  let B := E.symm '' transB l ε R
  let H := E.symm '' (transT l ε R ∪ transL l ε R)
  obtain ⟨hD,hO,hS,_,_,_,_,_,hOD,_,hSD,_,_,hB,hBD,hH,hHS,_,hSub⟩ :=
    native_rooms E hBig hε hεl hR hl haR
  have hSD' : S ⊆ D := subset_closure.trans hSD
  have hOD' : O ⊆ D := subset_closure.trans hOD
  refine ⟨hD,hSD',hOD',?_⟩
  obtain ⟨χ,hχ,hχc,hχsupp,hχO,hχgerm⟩ := hcut l ε R hε hεl hR (hl.trans haa) (haR.trans haa)
  have hDbox : (closedD l ε R : Set (ℝ × (fderiv ℝ θ p).ker)) ⊆
      Icc (-a) a ×ˢ closedBall (0 : (fderiv ℝ θ p).ker) a := closedD_subset_big hε hl haR
  have hDt := hDbox.trans hBig
  have hχD : tsupport χ ⊆ D := hχsupp.trans hSub
  have hχB : tsupport χ ⊆ closedBall p r := hχD.trans
    ((image_mono (roomD_subset_closedD.trans hDbox)).trans (hball.trans ball_subset_closedBall))
  obtain ⟨hθB,hθH,hθO⟩ := native_weight_heights E hE hκ hε hεl hR hκl hDt
  have hχtrans (x : (X n)) (hx : x ∉ B ∪ H) :
      (χ =ᶠ[nhds x] fun _ => (0 : ℝ)) ∨ χ =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    apply hχgerm x
    simpa only [B,H,image_union,union_assoc] using hx
  have hκsmall : κ*l ≤ 1/4 := by nlinarith [mul_pos hκ hε]
  let ψ (x : (X n)) := strictHeight κ (θ x)
  have hψ : Continuous ψ := hθ.continuous.sub (continuous_const.mul (hθ.continuous.pow 2))
  obtain ⟨hgapB,hgapH,hγ₁,hγ₂⟩ := strictExponent_bounds hκ (by linarith) hκsmall hε.le hε4

  obtain ⟨MB,hMB,hResB⟩ := exists_reference_scalar_collar_residual hL₀ hD hD
    Subset.rfl hB hBD hχ
  obtain ⟨MH,hMH,hResH⟩ := exists_reference_scalar_collar_residual hL₀ hD hS
    hSD' hH hHS hχ
  let M := max MB MH
  have hM : 0 ≤ M := hMB.trans (le_max_left _ _)
  refine ⟨2*Real.sqrt (C*M) + Real.exp ((strictHeight κ (-ε) - strictHeight κ (-l + 3*ε)) * max τ₀ 1),
    _,by positivity,hγ₁,hγ₂,?_⟩
  intro L hL he
  filter_upwards [hCar L hL he,hResB L hL he,hResH L hL he] with t hCarl hRB hRH
  apply interpolates_of_scalar_collars (hL.1 t) hD hO.measurableSet hSD' hOD' hB hH
    hχ hχc hχD hχB (fun x hx => hχO x (image_mono roomO_subset_closedO hx)) hχtrans hψ
    (sub_pos.mp hgapB) (sub_pos.mp hgapH) hC.le hM hτ₀ hθB hθH
    (fun x hx => hθO x (image_mono roomO_subset_closedO hx))
    (hCarl κ (by simpa only [abs_of_pos hκ] using hκr))
  · intro w hw hMem
    exact (hRB w hw hMem).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (MeasureTheory.integral_nonneg fun _ => sq_nonneg _))
  · intro w hw hMem
    exact (hRH w hw hMem).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (MeasureTheory.integral_nonneg fun _ => sq_nonneg _))

end CalderonPaper.ScalarElliptic
