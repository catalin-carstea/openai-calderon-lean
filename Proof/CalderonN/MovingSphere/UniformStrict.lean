module

public import Proof.CalderonN.MovingSphere.Strict
public import Proof.CalderonN.ProfileBounds

import Proof.CalderonN.ConnectionPerturbation
import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.SmoothMetricFrame
import Proof.CalderonN.NormalInverse
import Proof.CalderonN.ProductConformal
import Proof.CalderonN.SmallJetBounds
import Proof.CalderonN.JacobiCurvatureBounds
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN.MovingSphere

variable {dim : ℕ} [NeZero dim]
variable {normal : I dim}

set_option maxHeartbeats 2500000 in
/-- The actual conformal and dilated metrics satisfy the moving-sphere
strictness test with a common choice of degree, smallness, and radius
caps. The inverse normal map is shared across the regularization interval. -/
theorem exists_uniform_strict_conformal_spheres
    {Y Ω D : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hYc : IsCompact (closure Y)) (hYΩ : closure Y ⊆ Ω)
    (hDc : IsCompact D) (hΩD : Ω ⊆ D)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (hunit : g₁ 0 = 1) :
    ∃ (pmin : ℕ) (εmax : ℕ → ℝ) (Rmax : ℕ → ℝ → ℝ),
      (∀ p ≥ pmin, 0 < εmax p) ∧
      (∀ p ≥ pmin, ∀ ε ∈ Ioc (0 : ℝ) (εmax p), 0 < Rmax p ε) ∧
      ∀ p ≥ pmin, ∀ ε ∈ Ioc (0 : ℝ) (εmax p), ∀ R ∈ Ioc (0 : ℝ) (Rmax p ε),
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
        let γ := conformalReference (depthScale normal 4) g₁ lam
        let q₁ := dilatedMetric g₁ lam
        let q₂ := dilatedMetric g₂ lam
        ∀ {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)}, ContDiff ℝ ∞ E →
          NormalCoordinates Y Ω γ E (fun _ => ρ) →
          let N := normalPairDomain Y γ ρ E
          IsOpen N ∧ N ⊆ Ω ×ˢ Y ∧
          ∃ V : (X dim) × (X dim) → (X dim), ContDiffOn ℝ ∞ V N ∧
            (∀ z ∈ normalVelocityDomain Y γ ρ, V (E z,z.1) = z.2) ∧
            (∀ z ∈ N, (z.2,V z) ∈ normalVelocityDomain Y γ ρ ∧ E (z.2,V z) = z.1) ∧
            ∀ δ ∈ Ioc (0 : ℝ) 1,
              let r := shrinkingRadius R p (conformalDepth normal 4) δ
              ∀ z ∈ N, normalPhase γ V r z = 0 →
                smallJet γ q₂ z.2 ≤ ε * r z.2 →
                ProductStrictHessianAt q₁ q₂ (normalPhase γ V r) z := by
  let S := Icc (-1 : ℝ) 1
  let P := S ×ˢ D
  have hP : IsCompact P := isCompact_Icc.prod hDc
  let γ := conformalReference (depthScale normal 4) g₁
  let q₁ := dilatedMetric g₁
  let q₂ := dilatedMetric g₂
  have hγ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j) := by
    apply contDiffOn_univ.mp
    simpa only [mem_univ,ofPred_true] using
      contDiffOn_conformalReference_family_entry hg₁ (contDiff_depthScale (normal := normal) 4) i j
  have h₂ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => q₂ q.1 q.2 i j) :=
    (contDiffOn_univ.mp (hg₂.1 i j)).comp (contDiff_fst.smul contDiff_snd)
  have hp₁ (lam : ℝ) (y : (X dim)) : (q₁ lam y).PosDef := hg₁.2 _ (mem_univ _)
  have hp₂ (lam : ℝ) (y : (X dim)) : (q₂ lam y).PosDef := hg₂.2 _ (mem_univ _)
  have hpγ (lam : ℝ) (y : (X dim)) : (γ lam y).PosDef :=
    (hp₁ lam y).smul (depthScale_pos (normal := normal) 4 y)
  have hApos (lam : ℝ) (y : (X dim)) : (principalMetric (γ lam) (q₂ lam) y).PosDef :=
    (principal_posDef (hpγ lam y) (hp₂ lam y)).inv
  obtain ⟨B,hB,hCurv⟩ := exists_uniform_jacobiCurvatureTerm_bound hγ hpγ hP
  obtain ⟨C,hC,hConn⟩ := exists_uniform_connection_sub_bound_of_inverseJets hγ
    (contDiff_principalMetric_family_entry hγ h₂ hpγ hp₂) hpγ hApos hP
  obtain ⟨c,U,hc,hU,hBounds⟩ := exists_uniform_metric_comparison hP
    (fun i j => (hγ i j).continuous.continuousOn) (fun q _ => hpγ q.1 q.2)
  let K := max (max 1 c⁻¹) U
  have hK : 0 < K := zero_lt_one.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  have hi : K⁻¹ ≤ c := by
    have hh := (inv_le_inv₀ hK (inv_pos.mpr hc)).mpr ((le_max_right _ _).trans (le_max_left _ _))
    simpa only [inv_inv] using hh
  have hEll (lam : ℝ) (hlam : lam ∈ S) (y : (X dim)) (hy : y ∈ Ω) (v : (X dim)) :
      K⁻¹*‖v‖^2 ≤ metricPair (γ lam) y v v ∧ metricPair (γ lam) y v v ≤ K*‖v‖^2 := by
    have hb := hBounds (lam,y) ⟨hlam,hΩD hy⟩ v
    exact ⟨(mul_le_mul_of_nonneg_right hi (sq_nonneg _)).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
  let e (lam : ℝ) (y : (X dim)) := smoothMetricFrame (γ lam y)
  have hFrame (lam : ℝ) (y : (X dim)) (i j : (I dim)) :
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i = j then 1 else 0 :=
    smoothMetricFrame_orthonormal (hpγ lam y) i j
  have hS : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hF : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ y ∈ closure Y, ∀ i j,
      |e lam y i j| ≤ Real.sqrt K := by
    filter_upwards [hS] with lam hLam _ y hy i j
    have h := (hEll lam hLam y (hYΩ hy) (e lam y i)).1
    rw [hFrame lam y i i,ite_eq_left rfl,inv_mul_eq_div,div_le_iff₀ hK,one_mul] at h
    have ht : ‖e lam y i‖ ≤ Real.sqrt K := by
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rwa [Real.sq_sqrt hK.le]
    exact (((Real.norm_eq_abs _).trans_le (PiLp.norm_apply_le (e lam y i) j)) : _).trans ht
  obtain ⟨d,c₀,M,T,hd,hc₀,hM,Cj,hProfile⟩ :=
    exists_conformal_shrinkingRadius_profile hYc hg₁ hunit e (Real.sqrt_nonneg _) hF
  obtain ⟨p₀,rcap,hrcap,hStrict⟩ :=
    exists_normal_sphere_strictness_parameters (dim := dim) d c₀ K B C hd hc₀ hK hB hC
  choose εmax hεmax hStrictAt using
    fun p : ℕ => hStrict (max p p₀) (le_max_right p p₀)
  let pmin := max 2 p₀
  obtain ⟨L₀,hL₀⟩ := hYc.exists_bound_of_continuousOn (contDiff_conformalDepth (normal := normal) 4).continuous.continuousOn
  let L := Real.log (1 + Real.exp L₀)
  let Z (p : ℕ) := (p : ℝ)^2 * M^2 * (Real.log (1 + Real.exp T))^(p-2)
  let Rmax (p : ℕ) (ε : ℝ) := min (rcap / L^p) (ε / Z p)
  have hL : 0 < L := Real.log_pos (by linarith [Real.exp_pos L₀])
  have hZ (p : ℕ) (hp : 2 ≤ p) : 0 < Z p := by
    have hp' : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    have ht : 0 < Real.log (1 + Real.exp T) := Real.log_pos (by linarith [Real.exp_pos T])
    dsimp only [Z]
    positivity
  refine ⟨pmin,εmax,Rmax,fun p _ => hεmax p,?_⟩
  refine ⟨fun p hp ε hε => lt_min (div_pos hrcap (pow_pos hL _))
    (div_pos hε.1 (hZ p ((le_max_left _ _).trans hp))),?_⟩
  intro p hp ε hε R hR
  have hp₂' : 2 ≤ p := (le_max_left _ _).trans hp
  have hp₀' : p₀ ≤ p := (le_max_right _ _).trans hp
  have hMove := @hStrictAt p ε hε
  rw [max_eq_left hp₀'] at hMove
  have hRL : R*L^p ≤ rcap := (le_div_iff₀ (pow_pos hL _)).mp (hR.2.trans (min_le_left _ _))
  have hRZ : R*Z p ≤ ε := (le_div_iff₀ (hZ p hp₂')).mp (hR.2.trans (min_le_right _ _))
  filter_upwards [hS,hProfile] with lam hLam hProf hLamPos
  dsimp only
  intro ρ E hE hNormal
  have hgγ : SmoothMetric univ (γ lam) :=
    ⟨fun i j => ((hγ i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,fun y _ => hpγ lam y⟩
  have hq₁ : SmoothMetric univ (q₁ lam) := by
    have hs : ContDiff ℝ ∞ (fun y : (X dim) => lam • y) :=
      (contDiff_id : ContDiff ℝ ∞ (id : (X dim) → (X dim))).const_smul lam
    exact ⟨fun i j => ((contDiffOn_univ.mp (hg₁.1 i j)).comp hs).contDiffOn,fun y _ => hp₁ lam y⟩
  have hq₂ : SmoothMetric univ (q₂ lam) :=
    ⟨fun i j => ((h₂ i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,fun y _ => hp₂ lam y⟩
  have hγY : SmoothMetric Y (γ lam) :=
    ⟨fun i j => (hgγ.1 i j).mono (subset_univ _),fun y _ => hpγ lam y⟩
  obtain ⟨hOpen,hSub,V,hV,hExact,hInv⟩ := exists_normal_inverse_velocity hY hγY hNormal
  refine ⟨hOpen,hSub,V,hV,hExact,hInv,fun δ hδ => ?_⟩
  obtain ⟨hPr,hβ⟩ := hProf hLamPos δ hδ hp₂' R hR.1
  let r := shrinkingRadius R p (conformalDepth normal 4) δ
  have hPrY : Profile Y (γ lam) (e lam) r (d * (p : ℝ)) c₀ Cj :=
    ⟨hPr.1.mono subset_closure,fun y hy => hPr.2 y (subset_closure hy)⟩
  intro z hz hZero hSmall
  have hy : z.2 ∈ Y := (hInv z hz).1.1
  have hyΩ : z.2 ∈ Ω := hYΩ (subset_closure hy)
  have hrpos : 0 < r z.2 := (hPrY.2 z.2 hy).1
  have hrCap : r z.2 ≤ rcap := by
    have hD := (le_abs_self _).trans (hL₀ z.2 (subset_closure hy))
    have hSoft : softplus δ (conformalDepth normal 4 z.2) ≤ L := by
      refine (strictMonoOn_softplus_scale (conformalDepth normal 4 z.2)).monotoneOn
        hδ.1 zero_lt_one hδ.2 |>.trans ?_
      simp only [softplus,div_one,one_mul,L]
      exact Real.log_le_log (by positivity) (by linarith [Real.exp_le_exp.mpr hD])
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (softplus_pos hδ.1 _).le hSoft p)
      hR.1.le).trans hRL
  have hCurv' (x : (X dim)) (hx : x ∈ Ω) :=
    hCurv (lam,x) ⟨hLam,hΩD hx⟩
  have hConn' (u v : (X dim)) :
      ‖connection (principalMetric (γ lam) (q₂ lam)) z.2 u v - connection (γ lam) z.2 u v‖ ≤
        C*(ε*r z.2)*‖u‖*‖v‖ := by
    apply hConn (lam,z.2) ⟨hLam,hΩD hyΩ⟩ (ε*r z.2) (mul_nonneg hε.1.le hrpos.le) ?_ ?_
    · intro i j
      rw [inverse_principalMetric (hpγ lam z.2) (hp₂ lam z.2)]
      exact (abs_principal_sub_inverse_entry_le_smallJet (γ lam) (q₂ lam) z.2 i j).trans hSmall
    · intro k i j
      simp_rw [fun y => inverse_principalMetric (hpγ lam y) (hp₂ lam y)]
      exact (abs_coordDeriv_principal_sub_inverse_le_smallJet (γ lam) (q₂ lam) z.2 k i j).trans hSmall
  have hTest := hMove hY hΩ ((subset_closure : Y ⊆ closure Y).trans hYΩ) hgγ hq₂ hE
    hNormal hPrY hOpen hV hInv (hEll lam hLam) hCurv' z hz hZero hrCap
    (hPrY.2 z.2 hy).2.1 ((hβ z.2 (subset_closure hy)).trans (by
      simpa only [Z,mul_assoc] using hRZ)) hSmall (hFrame lam z.2) hConn'
  have hDφ : DifferentiableAt ℝ (normalPhase (γ lam) V r) z := by
    have hsm := contDiffOn_normalPhase hγY (fun z hz => (hInv z hz).1.1) hV hPrY.1
    exact (hsm.contDiffAt (hOpen.mem_nhds hz)).differentiableAt (by simp)
  apply (productStrictHessianAt_conformal_iff hq₁ hq₂ hDφ (c₁ := depthScale normal 4) (c₂ := fun _ => (1 : ℝ))
    ((contDiff_depthScale (normal := normal) 4).differentiable (by simp) z.1) (differentiableAt_const _)
    (depthScale_pos (normal := normal) 4 z.1) (by norm_num)).mp
  have heq : (fun x => depthScale normal 4 x • q₁ lam x) = γ lam := rfl
  simpa only [one_smul,heq] using hTest

end CalderonN.MovingSphere
