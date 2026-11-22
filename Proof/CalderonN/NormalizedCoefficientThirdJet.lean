module

public import Proof.CalderonN.NormalizedCoefficientRemainderC2
public import Proof.CalderonN.AffineNormalizedCenterJets

import Mathlib.Tactic

/-! The same joint coefficient envelope also controls the third angular
jet. The linear rescaling gives three powers of the radius. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem norm_iteratedFDeriv_comp_continuousLinearMap_le_at
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] F) (f : F → G) (z : E) (k : ℕ) (hf : ContDiffAt ℝ ∞ f (L z)) :
    ‖iteratedFDeriv ℝ k (f ∘ L) z‖ ≤ ‖iteratedFDeriv ℝ k f (L z)‖*‖L‖^k := by
  obtain ⟨S,hS,hfS⟩ := hf.contDiffOn (show (k:ℕ∞ω) ≤ ∞ by simp) (by simp)
  obtain ⟨U,hUS,hU,hz⟩ := _root_.mem_nhds_iff.mp hS
  have hPre := hU.preimage L.continuous
  have hEq := L.iteratedFDerivWithin_comp_right (hfS.mono hUS)
    hU.uniqueDiffOn hPre.uniqueDiffOn hz (i:=k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hPre hz,iteratedFDerivWithin_of_isOpen k hU hz] at hEq
  rw [hEq]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    ((iteratedFDeriv ℝ k f (L z)).norm_compContinuousLinearMap_le (fun _ => L))

theorem uniform_actual_normalized_coefficient_third_jet (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Q : ℝ, 0 < η ∧ 0 ≤ Q ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, ∀ z ∈ closedBall (0 : X dim) 1,
        ‖iteratedFDeriv ℝ 3 (normalizedFirstCoefficientRemainder d y) z‖ ≤ Q*(d.radius y)^2 := by
  obtain ⟨η,hη,hNormal⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega : 2 ≤ m)
    K ρ c₀ M Cj hK hρ 1 zero_le_one
  obtain ⟨Q,hQ,hJet⟩ := exists_actualCenterCoefficientFamily_jet_bound dim hm K M hK
  refine ⟨min η (min 1 (ρ/2)),Q,lt_min hη (lt_min zero_lt_one (half_pos hρ)),hQ,?_⟩
  intro floor hf ε he hs d hd y hy z hz
  let r := d.radius y
  let F := actualCenterCoefficientFamilyJet d y (0 : X dim)
  let P := frameVectorLinear d.frame y
  let L := r • (ContinuousLinearMap.inr ℝ ℝ (X dim))
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε :=
    (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
  have hr₁ := hrε.trans (hs.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrρ : r < ρ := (hrε.trans (hs.trans ((min_le_right _ _).trans (min_le_right _ _)))).trans_lt
    (half_lt_self hρ)
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hzD := frameVector_mem_disk d.γ d.frame y z 1 hFrame hz
  have hNormal' := hNormal floor hf ε he (hs.trans (min_le_left _ _)) d hd y hy _ hzD
  have hVel : P (r • z) = r • frameVector d.frame y z := by rw [map_smul,frameVectorLinear_apply]
  have hStrict : metricPair d.γ y (P (r • z)) (P (r • z)) < (max ρ r)^2 := by
    rw [hVel,metricPair_smul_left,metricPair_smul_right]
    have hScaled := mul_le_mul_of_nonneg_left (show
      metricPair d.γ y (frameVector d.frame y z) (frameVector d.frame y z) ≤ 1^2 from hzD) (sq_nonneg r)
    have hR := (sq_lt_sq₀ hr.le ((le_max_left ρ r).trans' hρ.le)).mpr
      (hrρ.trans_le (le_max_left ρ r))
    nlinarith only [hScaled,hR]
  have hV : ‖r • z‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz) hr.le).trans
      (by rw [mul_one]; exact hr₁)
  obtain ⟨hF,hBound⟩ := hJet hY hΩ hd y hy (0 : X dim) (r • z) (by simpa using zero_le_one.trans hK)
    hV (by rw [hVel]; exact hNormal'.1.2) hStrict (by rw [hVel]; exact hNormal'.2.2.2.1)
  have hJ : ‖ContinuousLinearMap.inr ℝ ℝ (X dim)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    rw [one_mul]
    change ‖((0:ℝ),w)‖ ≤ ‖w‖
    simp [Prod.norm_mk,norm_nonneg]
  have hLnorm : ‖L‖ ≤ r := by
    change ‖r • ContinuousLinearMap.inr ℝ ℝ (X dim)‖ ≤ r
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hJ hr.le).trans_eq (mul_one _)
  have hL (w : X dim) : L w = (0,r • w) := by
    change r • ((0:ℝ),w) = _
    simp
  have hEq (w : X dim) : (F ∘ L) w =
      firstNormalVelocityCoefficient d y (r • frameVector d.frame y w) := by
    rw [Function.comp_apply,hL]
    unfold F actualCenterCoefficientFamilyJet affineNormalCoefficient affineNormalPullbackData
      affineNormalInput affineCenterFrame firstNormalVelocityCoefficient
    simp [centerInverseDensity,frameVectorLinear_apply]
  let Ell := (r • (firstDensityCenterLinear d y).smulRight (1 : Mat dim))
  let C : X dim → Mat dim := fun w => 1+Ell w
  have hC3 : iteratedFDeriv ℝ 3 C z = 0 := by
    have hC' : fderiv ℝ C = fun _ => Ell := funext fun w => (Ell.hasFDerivAt.const_add (1 : Mat dim)).fderiv
    rw [show (3:ℕ) = 2+1 by decide,iteratedFDeriv_succ_eq_comp_right,hC']
    simp [iteratedFDeriv_const_of_ne (by omega : (2:ℕ) ≠ 0)]
  have hComp : ContDiffAt ℝ ∞ (F ∘ L) z :=
    (show ContDiffAt ℝ ∞ F (L z) by rw [hL]; exact hF).comp z L.contDiff.contDiffAt
  have hR : normalizedFirstCoefficientRemainder d y = (F ∘ L)-C := by
    funext w
    rw [Pi.sub_apply,hEq,normalizedFirstCoefficientRemainder]
    congr 1
    change ((1+r*firstDensityCenterLinear d y w) • (1 : Mat dim)) =
      1+r • (firstDensityCenterLinear d y w • (1 : Mat dim))
    rw [add_smul,one_smul,mul_smul]
  have hN : ‖iteratedFDeriv ℝ 3 (F ∘ L) z‖ ≤ Q*r^3 :=
    (norm_iteratedFDeriv_comp_continuousLinearMap_le_at L F z 3 (by rw [hL]; exact hF)).trans
      (mul_le_mul (by rw [hL]; exact hBound 3 le_rfl)
        (pow_le_pow_left₀ (norm_nonneg _) hLnorm 3) (by positivity) hQ)
  have hCtop : ContDiffAt ℝ ∞ C z := (contDiff_const.add Ell.contDiff).contDiffAt
  have hC : ContDiffAt ℝ (3:ℕ∞ω) C z := hCtop.of_le (by simp)
  rw [hR,iteratedFDeriv_sub_apply (i:=3) (hComp.of_le (by simp)) hC,hC3,sub_zero]
  exact hN.trans (mul_le_mul_of_nonneg_left (by
    calc
      r^3 = r^2*r := by ring
      _ ≤ r^2*1 := mul_le_mul_of_nonneg_left hr₁ (sq_nonneg r)
      _ = _ := mul_one _) hQ)

end CalderonN
