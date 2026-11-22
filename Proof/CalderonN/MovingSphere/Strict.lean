module

public import Proof.CalderonN.NormalTransportedPhase
public import Proof.CalderonN.PrincipalMetric

import Proof.CalderonN.FramedConnectionCorrection
import Proof.CalderonN.MovingSphere.FramedEnergy
import Proof.CalderonN.ProductConformal
import Proof.CalderonN.SmallJetBounds
import Mathlib.Tactic

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace Topology

namespace CalderonN.MovingSphere

variable {dim : ℕ} [NeZero dim]

set_option maxHeartbeats 1800000 in
/-- Uniform geometry and the protected tensor smallness imply the strict
Hessian test at every point of an actual moving normal sphere. -/
theorem exists_normal_sphere_strictness_parameters
    (cβ c₀ K B C : ℝ) (hcβ : 0 < cβ) (hc₀ : 0 < c₀) (hK : 0 < K) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ pmin : ℕ, ∃ rcap > (0 : ℝ), ∀ m : ℕ, pmin ≤ m →
      ∃ εcap > (0 : ℝ), ∀ ε ∈ Ioc (0 : ℝ) εcap,
      ∀ {Y Ω : Set (X dim)}, IsOpen Y → IsOpen Ω → Y ⊆ Ω →
      ∀ {γ g : (MetricField dim)}, SmoothMetric univ γ → SmoothMetric univ g →
      ∀ {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}, ContDiff ℝ ∞ E →
      NormalCoordinates Y Ω γ E (fun _ => ρ) →
      ∀ {r : (X dim) → ℝ} {e : (Frame dim)} {floor : ℝ} {Cj : Fin 9 → ℝ},
      Profile Y γ e r floor c₀ Cj →
      IsOpen (normalPairDomain Y γ ρ E) →
      ContDiffOn ℝ ∞ V (normalPairDomain Y γ ρ E) →
      (∀ q ∈ normalPairDomain Y γ ρ E,
        (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1) →
      (∀ x ∈ Ω, ∀ u, K⁻¹ * ‖u‖^2 ≤ metricPair γ x u u ∧
        metricPair γ x u u ≤ K * ‖u‖^2) →
      (∀ x ∈ Ω, ∀ v J : (X dim), ‖jacobiCurvatureTerm γ x v J‖ ≤ B * ‖v‖^2 * ‖J‖) →
      ∀ q ∈ normalPairDomain Y γ ρ E, normalPhase γ V r q = 0 →
      r q.2 ≤ rcap → cβ * (m : ℝ) ≤ beta γ r q.2 →
      r q.2 * (beta γ r q.2)^2 ≤ ε →
      smallJet γ g q.2 ≤ ε * r q.2 →
      (∀ i j, metricPair γ q.2 (e q.2 i) (e q.2 j) = if i = j then 1 else 0) →
      (∀ u v : (X dim), ‖connection (principalMetric γ g) q.2 u v - connection γ q.2 u v‖ ≤
        C * (ε * r q.2) * ‖u‖ * ‖v‖) →
      ProductStrictHessianAt γ g (normalPhase γ V r) q := by
  let D₂ := (dim : ℝ)^2*K
  let Cr := 2*B*K^2
  let Cg := 2*C*K*Real.sqrt K
  obtain ⟨m₀,_,hE⟩ := exists_native_framed_energy_strictness_parameters
    cβ c₀ 0 D₂ 0 Cr Cg hcβ hc₀ (by norm_num) (by positivity) (by norm_num)
    (by positivity) (by positivity)
  obtain ⟨n,hn⟩ := exists_nat_gt (1/cβ)
  let rcap := min 1 (min (1/(2*(B*K^2+1))) (1/(320*(D₂+1))))
  have hrcap : 0 < rcap := by dsimp [rcap]; positivity
  refine ⟨max m₀ n,rcap,hrcap,fun m hm => ?_⟩
  obtain ⟨ε₀,hε₀,hε₁,hStrict⟩ := hE m ((le_max_left _ _).trans hm)
  let εcap := min ε₀ (1/8)
  have hεcap : 0 < εcap := lt_min hε₀ (by norm_num)
  refine ⟨εcap,hεcap,fun ε hε => ?_⟩
  intro Y Ω hY hΩ hYΩ γ g hγ hg ρ E V hExp hNormal r e floor Cj hProf hD hV hInv
    hEll hCurv q hq hSphere hR hβ hβsq hSmall he₂ hConn
  have hy : q.2 ∈ Y := (hInv q hq).1.1
  have hr : 0 < r q.2 := (hProf.2 q.2 hy).1
  have hr₁ : r q.2 ≤ 1 := hR.trans (min_le_left _ _)
  have hε₀' : ε ≤ ε₀ := hε.2.trans (min_le_left _ _)
  have hε₁' : ε ≤ 1 := hε₀'.trans hε₁
  have hε₈ : ε ≤ 1/8 := hε.2.trans (min_le_right _ _)
  have hBKr : B*K^2*(r q.2)^2 ≤ 1/2 := by
    have hR' : r q.2 ≤ 1/(2*(B*K^2+1)) :=
      hR.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h := (le_div_iff₀ (by positivity : 0 < 2*(B*K^2+1))).mp hR'
    have hh := mul_le_mul_of_nonneg_left hr₁ (by positivity : 0 ≤ B*K^2*r q.2)
    nlinarith only [h,hh,hr.le]
  have hD₂ : D₂*ε*r q.2 ≤ 1/320 := by
    have hR' : r q.2 ≤ 1/(320*(D₂+1)) :=
      hR.trans ((min_le_right _ _).trans (min_le_right _ _))
    have h := (le_div_iff₀ (by positivity : 0 < 320*(D₂+1))).mp hR'
    have hh := mul_le_mul_of_nonneg_right hε₁' (by positivity : 0 ≤ D₂*r q.2)
    nlinarith only [h,hh,hr.le]
  have hβ₁ : 1 ≤ beta γ r q.2 := by
    have hn' : (n : ℝ) ≤ m := by exact_mod_cast (le_max_right m₀ n).trans hm
    have hh := (div_lt_iff₀ hcβ).mp hn
    linarith only [hh,mul_le_mul_of_nonneg_left hn' hcβ.le,hβ]
  have hβle : r q.2 * beta γ r q.2 ≤ ε := by
    have h := mul_le_mul_of_nonneg_right hβ₁ (zero_le_one.trans hβ₁)
    rw [one_mul,← pow_two] at h
    exact (mul_le_mul_of_nonneg_left h hr.le).trans hβsq
  let z := (r q.2)⁻¹ • frameCoordinates γ q.2 (e q.2) (V q)
  let b := frameCoordinates γ q.2 (e q.2) (chartMetricGradient γ r q.2)
  let φ := normalPhase γ V r
  let A := principalMetric γ g
  obtain ⟨hz,hb,e₁,he₁,hEst⟩ := exists_normalPhase_framed_estimates
    hY hΩ hγ hExp hNormal hYΩ hProf hD hV hInv hq hSphere he₂ hB hK hBKr hEll hCurv
  have hz' : ‖z‖ = 1 := hz
  have hb' : ‖b‖ = r q.2 * beta γ r q.2 := hb
  have hb₈ : ‖b‖ ≤ 1/8 := hb'.le.trans (hβle.trans hε₈)
  have hsum : ‖z+b‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hz']; linarith only [hb₈])
  have hsumne : z+b ≠ 0 := by
    intro h
    have h' : z = -b := eq_neg_of_add_eq_zero_left h
    have h'' : ‖z‖ = ‖b‖ := (congrArg norm h').trans (norm_neg _)
    linarith only [hz',h'',hb₈]
  have hγY : SmoothMetric Y γ := ⟨fun i j => (hγ.1 i j).mono (subset_univ _),
    fun x _ => hγ.2 x (mem_univ _)⟩
  have hφsmooth : ContDiffOn ℝ ∞ φ (normalPairDomain Y γ ρ E) :=
    contDiffOn_normalPhase hγY (fun q hq => (hInv q hq).1.1) hV hProf.1
  have hφ : DifferentiableAt ℝ φ q :=
    (hφsmooth.contDiffAt (hD.mem_nhds hq)).differentiableAt (by simp)
  have hFirst (u : (X dim) × (X dim)) :
      fderiv ℝ φ q u = r q.2 * (⟪z,frameCoordinatesL γ q.1 e₁ u.1⟫_ℝ -
        ⟪z+b,frameCoordinatesL γ q.2 (e q.2) u.2⟫_ℝ) := by
    simpa only [frameCoordinatesL_apply] using (hEst u).1
  have hSecond (v : (X dim)) :
      fderiv ℝ φ q (0,v) = -r q.2 * ⟪z+b,frameCoordinatesL γ q.2 (e q.2) v⟫_ℝ := by
    rw [hFirst]
    simp only [map_zero,inner_zero_right,zero_sub,mul_neg,neg_mul]
  let T := frameCometricOperator γ q.2 (e q.2) (A q.2)⁻¹
  let J := frameMetricOperator (A q.2) (e q.2)
  have hγp := hγ.2 q.2 (mem_univ _)
  have hgp := hg.2 q.2 (mem_univ _)
  have hA : (A q.2).PosDef := (principal_posDef hγp hgp).inv
  have hT : ‖T - ContinuousLinearMap.id ℝ (X dim)‖ ≤ D₂*ε*r q.2 := by
    refine (norm_frameCometricOperator_sub_id_le γ q.2 (e q.2) he₂ hγp hK.le
      (fun v => (hEll q.2 (hYΩ hy) v).2) (A q.2)⁻¹).trans ?_
    have ht : ‖(Matrix.toEuclideanCLM (n := (I dim)) (𝕜 := ℝ)
        ((A q.2)⁻¹ - (γ q.2)⁻¹) : (X dim) →L[ℝ] (X dim))‖ ≤ (dim : ℝ)^2*(ε*r q.2) := by
      rw [show (A q.2)⁻¹ = principal γ g q.2 from inverse_principalMetric hγp hgp]
      exact norm_toEuclideanCLM_le_of_entries _ (mul_nonneg hε.1.le hr.le) fun i j =>
        (abs_principal_sub_inverse_entry_le_smallJet γ g q.2 i j).trans hSmall
    exact (mul_le_mul_of_nonneg_left ht hK.le).trans_eq (by dsimp [D₂]; ring)
  let H := framedProductHessian γ A φ q e₁ (e q.2)
  have hH (U W : (X dim)) :
      ‖U-W‖^2-2*⟪b,W⟫_ℝ^2+c₀*beta γ r q.2*(r q.2)^2*‖W‖^2-
        Cr*(r q.2)^2*(‖U‖+‖W‖)^2-Cg*ε*(r q.2)^2*‖W‖^2 ≤ H U W := by
    have hlow := (hEst (frameVectorL e₁ U,frameVectorL (e q.2) W)).2
    simp only [← frameCoordinatesL_apply,frameCoordinatesL_frameVectorL γ q.1 e₁ he₁,
      frameCoordinatesL_frameVectorL γ q.2 (e q.2) he₂] at hlow
    rw [frameCoordinatesL_apply] at hlow
    have hchange := framedProductHessian_le_add_connectionError e₁ (e q.2) he₂
      hr.le hε.1.le hK hC (hEll q.2 (hYΩ hy)) hsum hSecond hConn U W
    change _ ≤ framedProductHessian γ γ φ q e₁ (e q.2) U W at hlow
    change _ ≤ H U W + Cg*ε*(r q.2)^2*‖W‖^2 at hchange
    exact (sub_le_iff_le_add).mpr (hlow.trans hchange)
  have hGeometric : ProductStrictHessianAt γ A φ q := by
    apply productStrictHessianAt_of_framedHessian hφ e₁ (e q.2) he₁ he₂
      (hγ.2 _ (mem_univ _)) hA hr hz' hsumne hFirst
    dsimp only
    intro U W hU hUU hW hWW
    have h := hStrict ε hε.1.le hε₀' (beta γ r q.2) (r q.2) hβ hr hr₁
      (by norm_num) hD₂ (ContinuousLinearMap.id ℝ (X dim)) (ContinuousLinearMap.id ℝ (X dim)) T J
      z b 0 U W hz' hb₈ (by simp) hb'.le (by simp) (by simp) hT (fun _ => rfl)
      (frameCometricOperator_frameMetricOperator γ q.2 (e q.2) he₂ _ hA)
      hU (by simpa [real_inner_self_eq_norm_sq,hz'] using hUU)
      (by simpa using hW) (by simpa using hWW) H hH
    simpa only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq,hz',one_pow,
      inv_one,one_smul,add_zero] using h
  have hscale : A = fun x => principalMetricScale γ g x • g x :=
    funext fun x => principalMetric_eq_smul (hγ.2 x (mem_univ _)) (hg.2 x (mem_univ _))
  apply (productStrictHessianAt_conformal_iff hγ hg hφ
    (c₁ := fun _ => (1 : ℝ)) (c₂ := principalMetricScale γ g)
    (differentiableAt_const _)
    ((contDiffOn_univ.mp (contDiffOn_principalMetricScale hγ hg)).differentiable (by simp) q.2)
    (by norm_num) (principalMetricScale_pos hγp hgp)).mp
  simpa only [one_smul,hscale] using hGeometric

end CalderonN.MovingSphere
