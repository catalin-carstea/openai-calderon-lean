module

public import Proof.CalderonN.GreenSourceTesting
import Proof.CalderonN.WeakFixedBallSmooth
import Proof.CalderonN.CutoffSourceRepresentative
import Proof.CalderonN.InteriorSourceScale
import Proof.CalderonN.FixedBallWeakSource
import Mathlib.Tactic

public section

/-! The normalized weak source solution supplies the classical solution
used in Green testing. On the source-free ball the critical Sobolev
bound and interior point estimate give the factor `r^(2-n/2)`. -/
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal Distributions Gradient Matrix.Norms.Elementwise

namespace CalderonN
open TauCeti TauCeti.PDE
variable {n : ℕ}

set_option maxHeartbeats 5000000 in
theorem separated_classical_source_estimate (hn : 3 ≤ n) : SeparatedClassicalSourceEstimate n := by
  let : NeZero n := ⟨by omega⟩
  let V := fixedBallOpens n
  let B := ball (0 : X n) 1
  let U : Opens (X n) := ⟨ball (0 : X n) (3/4), isOpen_ball⟩
  let μ := (volume : Measure (X n)).restrict V
  have hUB : U ≤ V := ball_subset_ball (by norm_num)
  have hn0 : 0 < n := by omega
  have hμ : IsFiniteMeasure μ := ⟨by
    simpa only [μ,V,Measure.restrict_apply_univ,fixedBallOpens,TopologicalSpace.Opens.coe_mk] using
      (measure_ball_lt_top (μ := (volume : Measure (X n))) (x := (0 : X n)) (r := (1 : ℝ)))⟩
  intro a ha _ hs lo hi he
  obtain ⟨C,hC,hSol⟩ := exists_fixedBall_weak_source_gradient hn ha.continuous he
  obtain ⟨D,hD,hRep⟩ := exists_cutoff_source_rep_bound (n := n)
  obtain ⟨M,hM,hPoint⟩ := exists_rescaled_source_point_bound ha hs he
  let v₁ := ((volume : Measure (X n)).real B) ^ (1 / (n : ℝ))
  have hv₁ : 0 ≤ v₁ := Real.rpow_nonneg ENNReal.toReal_nonneg _
  let K := C*v₁
  have hK : 0 ≤ K := mul_nonneg hC.le hv₁
  let J := (v₁+1)*K
  let N := max 1 (max (D*J) (M*(v₁*K)))
  refine ⟨N,zero_lt_one.trans_le (le_max_left _ _),?_⟩
  intro y hy x r hr hBall hSep f hf hfK hSupp
  let A := ball x r
  let T := ball y r
  let ν := (volume : Measure (X n)).restrict T
  have hAC : A ⊆ closedBall (0 : X n) (1/2) := ball_subset_closedBall.trans hBall
  have hAB : A ⊆ B := hAC.trans (closedBall_subset_ball (by norm_num))
  have hTU : T ⊆ U := by
    intro z hz
    have he₁ : dist z y < r := mem_ball.mp hz
    have he₂ : dist y (0 : X n) ≤ 1/4 := mem_closedBall.mp hy
    exact mem_ball.mpr ((dist_triangle z y (0 : X n)).trans_lt (by linarith [hr.2]))
  have hTB : T ⊆ B := hTU.trans hUB
  have hν : IsFiniteMeasure ν := ⟨by
    simpa only [ν,Measure.restrict_apply_univ,T] using
      (measure_ball_lt_top (μ := (volume : Measure (X n))) (x := y) (r := r))⟩
  have hfLp : MemLp f 2 μ := hf.continuous.memLp_of_hasCompactSupport hfK
  let F := hfLp.toLp f
  have hF : ⇑F =ᵐ[μ] f := hfLp.coeFn_toLp
  have hFout : ∀ᵐ z ∂μ, z ∉ A → F z = 0 := by
    filter_upwards [hF] with z hz hout
    exact hz.trans (Function.notMem_support.mp (fun h => hout (hSupp h)))
  obtain ⟨u,hu,hGrad,hQu,hQ⟩ := hSol F A isOpen_ball.measurableSet hFout
  let w : FixedBallH1 n := u
  let Fnorm := (eLpNorm f 2 μ).toReal
  have hFn : ‖F‖ = Fnorm := Lp.norm_toLp f hfLp
  have hFnonneg : 0 ≤ Fnorm := ENNReal.toReal_nonneg
  have hAr : (μ.real A) ^ (1 / (n : ℝ)) = r*v₁ := by
    have hm : μ.real A = (volume : Measure (X n)).real A := by
      have hAV : ball x r ⊆ (V : Set (X n)) := hAB
      change ((volume : Measure (X n)).restrict (V : Set (X n))).real (ball x r) =
        (volume : Measure (X n)).real (ball x r)
      rw [measureReal_def, measureReal_def, Measure.restrict_apply isOpen_ball.measurableSet,
        inter_eq_left.mpr hAV]
    rw [hm]
    exact volume_real_ball_one_div_power hn0 x hr.1
  rw [hAr,hFn,show C * (r*v₁) * Fnorm = K*r*Fnorm by dsimp [K]; ring] at hGrad hQ
  have hW₂ : ‖W1p.value w‖ ≤ v₁ * (K*r*Fnorm) := by
    rw [Lp.norm_def]
    refine (eLpNorm_two_toReal_le_volume_one_div_eLpNorm_critical hn le_rfl hQu).trans ?_
    have hmeasure : (μ.real univ) ^ (1 / (n : ℝ)) = v₁ := by
      change (((volume : Measure (X n)).restrict B).real univ) ^ (1 / (n : ℝ)) = _
      rw [measureReal_def, Measure.restrict_apply_univ, ← measureReal_def]
    rw [hmeasure]
    exact mul_le_mul_of_nonneg_left hQ hv₁
  have hW : ‖w‖ ≤ J*r*Fnorm := by
    calc ‖w‖ ≤ ‖W1p.value w‖ + ‖W1p.gradient w‖ := W1p.norm_le_norm_value_add_norm_gradient w
      _ ≤ v₁*(K*r*Fnorm) + K*r*Fnorm := add_le_add hW₂ hGrad
      _ = J*r*Fnorm := by dsimp [J]; ring
  obtain ⟨b₀,hb₀,hb₀eq⟩ := exists_fixedBall_smooth_interior_rep ha he hf hF hu
  obtain ⟨b,hb,hbK,hbeq,hbGrad,hbNorm⟩ := hRep w b₀ hb₀ hb₀eq
  have hbEq : EqOn (negativeBallDivergence a b) f U :=
    negativeBallDivergence_eq_of_interior_representation hUB ha hf hb u hbeq F hF hu
  have hbT (z : X n) (hz : z ∈ T) : negativeBallDivergence a b z = 0 := by
    rw [hbEq (hTU hz)]
    apply Function.notMem_support.mp
    intro hsf
    have hxz : dist x z < r := by simpa [dist_comm] using mem_ball.mp (hSupp hsf)
    have hzy := mem_ball.mp hz
    linarith [dist_triangle x z y]
  have hLocal : Real.sqrt (∫ z in T, b z^2) ≤ (v₁*K) * r^2 * Fnorm := by
    have hb₂ : MemLp b 2 ν := hb.continuous.memLp_of_hasCompactSupport hbK
    have hbL : ⇑(W1p.value w) =ᵐ[ν] b := ae_restrict_of_ae_restrict_of_subset hTU hbeq
    have hνμ : ν ≤ μ := Measure.restrict_mono hTB le_rfl
    have hz := eLpNorm_two_toReal_le_volume_one_div_eLpNorm_critical hn hνμ hQu
    have hvN : (ν.real univ) ^ (1 / (n : ℝ)) = r*v₁ := by
      rw [measureReal_def,Measure.restrict_apply_univ,← measureReal_def]
      exact volume_real_ball_one_div_power hn0 y hr.1
    have hRoot := sqrt_integral_norm_sq_eq_eLpNorm_toReal hb₂
    simp only [Real.norm_eq_abs, sq_abs] at hRoot
    change Real.sqrt (∫ z, b z^2 ∂ν) ≤ _
    rw [hRoot, ← eLpNorm_congr_ae hbL]
    exact (by
      calc (eLpNorm (W1p.value w) 2 ν).toReal ≤ (r*v₁)*(K*r*Fnorm) :=
            (by rw [hvN] at hz; exact hz.trans (mul_le_mul_of_nonneg_left hQ (mul_nonneg hr.1.le hv₁)))
        _ = _ := by ring)
  have hMain : |b y| ≤ (M*(v₁*K)) * r ^ (2 - (n : ℝ)/2) * Fnorm := by
    calc
      _ ≤ M * r ^ (-(n : ℝ)/2) * Real.sqrt (∫ z in T, b z^2) := hPoint y hy r hr b hb hbT
      _ ≤ M * r ^ (-(n : ℝ)/2) * ((v₁*K) * r^2 * Fnorm) :=
        mul_le_mul_of_nonneg_left hLocal (mul_nonneg hM (Real.rpow_nonneg hr.1.le _))
      _ = _ := by
        rw [← Real.rpow_natCast, show ((2 : ℕ) : ℝ) = 2 by norm_num]
        rw [show r ^ (2 - (n : ℝ)/2) = r ^ (-(n : ℝ)/2) * r ^ (2 : ℝ) by
          rw [← Real.rpow_add hr.1]; congr 1; ring]
        ring
  have hDZ : D * J ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hMZ : M*(v₁*K) ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨b,hb,hbEq, ?_, ?_, ?_⟩
  · change |b y| ≤ N * r ^ (2 - (n : ℝ)/2) * Fnorm
    exact hMain.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hMZ (Real.rpow_nonneg hr.1.le _)) hFnonneg)
  · change (eLpNorm (fderiv ℝ b) 2 μ).toReal ≤ N*r*Fnorm
    refine hbGrad.trans ((mul_le_mul_of_nonneg_left hW hD.le).trans ?_)
    calc D * (J*r*Fnorm) = (D*J)*r*Fnorm := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDZ hr.1.le) hFnonneg
  · change (eLpNorm b 2 μ).toReal ≤ N*r*Fnorm
    refine hbNorm.trans ((mul_le_mul_of_nonneg_left hW hD.le).trans ?_)
    calc D * (J*r*Fnorm) = (D*J)*r*Fnorm := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDZ hr.1.le) hFnonneg

end CalderonN
