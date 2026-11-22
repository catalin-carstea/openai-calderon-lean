module

public import Proof.CalderonN.NormalizedRadialInverseJets
public import Proof.CalderonN.ActualSupportedGaussMultipliers

import Proof.CalderonN.ActualRelativeCoefficientGerms
import Proof.CalderonN.UniformLogRadiusChartJets
import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.CompactFiniteJets
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! The affine weight numerator and quadratic coefficient have the
same normalized joint chart bounds as the physical Dirichlet coefficient. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem conormalWeightQuadratic_add (A B : Mat dim) (z : X dim) :
    conormalWeightQuadratic (A+B) z = conormalWeightQuadratic A z+conormalWeightQuadratic B z := by
  simp only [conormalWeightQuadratic,Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

theorem conormalWeightQuadratic_smul (c : ℝ) (A : Mat dim) (z : X dim) :
    conormalWeightQuadratic (c • A) z = c*conormalWeightQuadratic A z := by
  simp only [conormalWeightQuadratic,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem conormalWeightQuadratic_one_on_sphere {z : X dim} (hz : z ∈ standardSphere dim) :
    conormalWeightQuadratic (1:Mat dim) z = 1 := by
  simpa [conormalWeightQuadratic,Matrix.one_apply,pow_two] using unitSphere_sum_sq (⟨z,hz⟩ : ↥(standardSphere dim))

private theorem contDiff_quadratic_jets :
    ContDiff ℝ ∞ (fun p : Mat dim × X dim => conormalWeightQuadratic p.1 p.2) := by
  unfold conormalWeightQuadratic
  apply ContDiff.sum
  intro i _
  refine ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp contDiff_snd).mul ?_
  exact ContDiff.sum fun j _ => ((matrixEntryL i j).contDiff.comp contDiff_fst).mul
    ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp contDiff_snd)

theorem uniform_actual_radialNumerator_factorization_germs (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (N : ℕ) (hN : N ≤ 8) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C D : ℝ, 0 < η ∧ 0 ≤ C ∧ 0 ≤ D ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ x ∈ Y,∃ (R : X dim → ℝ) (P L Q₂ : X dim × X dim → ℝ) (V : Set (X dim × X dim)),
        ContDiff ℝ ∞ R ∧ R =ᶠ[𝓝 x] d.radius ∧ ContDiff ℝ ∞ P ∧ ContDiff ℝ ∞ L ∧ ContDiff ℝ ∞ Q₂ ∧
        IsOpen V ∧ ({x} ×ˢ closedBall (0:X dim) 1) ⊆ V ∧
        (∀ y z,(y,z) ∈ V → y ∈ Y → z ∈ standardSphere dim →
          L (y,z) = firstDensityCenterLinear d y z ∧
          conormalWeightQuadratic (actualFramedCoefficientField d ((y,d.radius y),z)) z =
            1+d.radius y*P (y,z) ∧ P (y,z) = L (y,z)+d.radius y*Q₂ (y,z)) ∧
        ∀ z ∈ closedBall (0:X dim) 1,
          let β := beta d.γ d.radius x
          LocalSmoothJetBudget (fun q : X dim × X dim => R (x+β⁻¹ • q.1)) 0 N C ∧
          LocalSmoothJetBudget (fun q : X dim × X dim => P (x+β⁻¹ • q.1,z+q.2)) 0 N D ∧
          LocalSmoothJetBudget (fun q : X dim × X dim => L (x+β⁻¹ • q.1,z+q.2)) 0 N D ∧
          LocalSmoothJetBudget (fun q : X dim × X dim => Q₂ (x+β⁻¹ • q.1,z+q.2)) 0 N D := by
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨η₁,L₀,_,hη₁,hL₀,_,hA₁⟩ := uniform_actual_relativeCoefficient_factorization
    hn hY hΩ hYc N hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨η₂,A₀,hη₂,hA₀,hA₂⟩ := uniform_actual_framedCoefficient_radialRemainder
    hn hY hΩ hYc N hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨C₀,hC₀,hLog⟩ := uniform_background_logRadius_chart_jets hY hΩ hSub N hN (by omega) K M Cj hKp
  let E := X dim
  let CLog := max 1 C₀
  have hCLog : 1 ≤ CLog := le_max_left _ _
  obtain ⟨R₀,hR₀,hRad⟩ := uniform_radius_scaled_chart_jets hY N CLog hCLog
  obtain ⟨A₁,hA₁B,hComp⟩ := uniform_physicalChart_angular_jet_composition (Z:=E) (F:=Mat dim)
    hY N CLog hCLog
  let C := (N.factorial:ℝ)*R₀
  let A := max 1 (A₁*A₀)
  have hA : 1 ≤ A := le_max_left _ _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let Q : Mat dim × E → ℝ := fun p => conormalWeightQuadratic p.1 p.2
  have hQ : ContDiff ℝ ∞ Q := contDiff_quadratic_jets
  obtain ⟨B₀,hB₀,hQB⟩ := exists_uniform_finite_jet_bound
    ((isCompact_closedBall (0:Mat dim) A).prod (isCompact_closedBall (0:E) 1)) hQ N
  let B := (N.factorial:ℝ)*B₀*A^N
  let L₁ := ‖matrixEntryL (0:I dim) 0‖*((N.factorial:ℝ)*L₀)
  let D := L₁+(2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖*C*B+B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hL₁ : 0 ≤ L₁ := by dsimp only [L₁]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨min 1 (min η₁ η₂),C,D,lt_min zero_lt_one (lt_min hη₁ hη₂),hC,hD,?_⟩
  intro floor hFloor ε hε hs d hd hFrame x hx
  let β := beta d.γ d.radius x
  let r := d.radius
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hp (y : E) (hy : y ∈ Y) : 0 < r y := (hd.2.2.2.2.1.2 y hy).1
  have hr₁ : r x ≤ 1 := ((le_mul_of_one_le_right (hp x hx).le (one_le_pow₀ hβ)).trans
    (hd.2.2.2.2.2 x hx).2).trans (hs.trans (min_le_left _ _))
  have hLj n (hn' : n ≤ N) (hn₀ : 1 ≤ n) :
      ‖iteratedFDeriv ℝ n (fun y => Real.log (r y)) x‖ ≤ CLog*β^n :=
    (hLog d.γ d.g₁ d.g₂ d.frame hd.1 r floor c₀ hFloor hd.2.2.2.2.1 x hx n hn' hn₀).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans hβ) _))
  let U := Y ×ˢ ball (0:E) 2
  have hU : IsOpen U := hY.prod isOpen_ball
  let Sc := ({x} : Set E) ×ˢ closedBall (0:E) 1
  have hSc : IsCompact Sc := isCompact_singleton.prod (isCompact_closedBall _ _)
  have hSU : Sc ⊆ U := fun q hq => ⟨(show q.1=x from hq.1).symm ▸ hx,
    closedBall_subset_ball (by norm_num) hq.2⟩
  have hr := hd.2.2.2.2.1.1
  let j (q : E × E) := ((q.1,r q.1),q.2)
  let a (q : E × E) := actualFramedCoefficientRadialRemainder d (j q)
  let l (q : E × E) := firstDensityCenterLinear d q.1 q.2
  let p (q : E × E) := l q+r q.1*Q (a q,q.2)
  have hj : ContDiffOn ℝ ∞ j U := (contDiff_fst.contDiffOn.prodMk
    (hr.comp contDiff_fst.contDiffOn (fun _ h => h.1))).prodMk contDiff_snd.contDiffOn
  have hRemainder (y : E) (hy : y ∈ Y) (z : E) (hz : z ∈ closedBall (0:E) 2) :=
    hA₂ floor hFloor ε hε (hs.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd hFrame
      y hy (r y) (by rw [abs_of_pos (hp y hy)]; linarith [hp y hy]) z hz
  have ha : ContDiffOn ℝ ∞ a U := by
    change ContDiffOn ℝ ∞ (actualFramedCoefficientRadialRemainder d ∘ j) U
    intro q hq
    have h : ContDiffAt ℝ ∞ (actualFramedCoefficientRadialRemainder d) (j q) :=
      (hRemainder q.1 hq.1 q.2 (ball_subset_closedBall hq.2)).1.smooth
    exact h.comp_contDiffWithinAt q (hj q hq)
  have hl : ContDiffOn ℝ ∞ l U :=
    (((contDiffOn_actualFirstDensityCenterLinear hΩ hKp hd.1).comp contDiff_fst.contDiffOn
      (fun _ h => hSub h.1)).clm_apply contDiff_snd.contDiffOn)
  let q₂ (q : E × E) := Q (a q,q.2)
  have hQ₂ : ContDiffOn ℝ ∞ q₂ U := hQ.comp_contDiffOn (ha.prodMk contDiff_snd.contDiffOn)
  have hP : ContDiffOn ℝ ∞ p U :=
    hl.add ((hr.comp contDiff_fst.contDiffOn (fun _ h => h.1)).mul hQ₂)
  obtain ⟨P,hPg,_,V₁,hV₁,hSV₁,_,hPEq⟩ := exists_contDiff_extension_near_compact hU hSc hSU hP
  obtain ⟨L,hLg,_,V₂,hV₂,hSV₂,_,hLEq⟩ := exists_contDiff_extension_near_compact hU hSc hSU hl
  obtain ⟨Q₂,hQ₂g,_,V₃,hV₃,hSV₃,_,hQ₂Eq⟩ := exists_contDiff_extension_near_compact hU hSc hSU hQ₂
  obtain ⟨R,hRg,hREq⟩ := exists_global_smooth_germ_of_open r hY hr hx
  refine ⟨R,P,L,Q₂,(V₁∩V₂)∩V₃,hRg,hREq,hPg,hLg,hQ₂g,
    (hV₁.inter hV₂).inter hV₃,subset_inter (subset_inter hSV₁ hSV₂) hSV₃,?_,?_⟩
  · intro y z hV hy hz
    refine ⟨hLEq hV.1.2,?_,?_⟩
    · rw [hPEq hV.1.1,(hRemainder y hy z (closedBall_subset_closedBall (by norm_num) (sphere_subset_closedBall hz))).2,
        conormalWeightQuadratic_add,conormalWeightQuadratic_add,
        conormalWeightQuadratic_smul,conormalWeightQuadratic_smul,conormalWeightQuadratic_smul,
        conormalWeightQuadratic_one_on_sphere hz]
      change 1+r y*(l (y,z)*1)+(r y)^2*Q (a (y,z),z) = 1+r y*(l (y,z)+r y*Q (a (y,z),z))
      ring
    · rw [hPEq hV.1.1,hLEq hV.1.2,hQ₂Eq hV.2]
  intro z hz
  let f (q : E × E) := (x+β⁻¹ • q.1,z+q.2)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_const.add (contDiff_fst.const_smul _)).prodMk (contDiff_const.add contDiff_snd)
  have hf₀ : f 0 = (x,z) := by simp [f]
  obtain ⟨hRadJet,_⟩ := hRad r hr x hx hp β hβ hLj
  have hRJet := (hRadJet.const_smul (r x) (hp x hx).le)
  have hRR : (fun v : E => r x • (r (x+β⁻¹ • v)/r x)) = fun v => r (x+β⁻¹ • v) := by
    funext v
    change r x*(r (x+β⁻¹ • v)/r x) = _
    field_simp [(hp x hx).ne']
  rw [hRR] at hRJet
  let K₁ := ContinuousLinearMap.fst ℝ E E
  have hK₁ : ‖K₁‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    rw [one_mul]
    exact norm_fst_le v
  have hRJ : LocalSmoothJetBudget (fun q : E × E => r (f q).1) 0 N C := by
    have h := (hRJet.enlarge (mul_le_of_le_one_left hR₀ hr₁))
    have hh : LocalSmoothJetBudget (fun v : E => r (x+β⁻¹ • v)) (K₁ 0) N R₀ := by rw [map_zero]; exact h
    have h' := LocalSmoothJetBudget.linear_precomp K₁ (0:E × E) hh
    change LocalSmoothJetBudget ((fun v : E => r (x+β⁻¹ • v)) ∘ K₁) 0 N C
    simpa only [C,max_eq_left hK₁,one_pow,mul_one] using h'
  have hRrep : (fun q : E × E => R (x+β⁻¹ • q.1)) =ᶠ[𝓝 0] fun q => r (f q).1 := by
    have hc : ContinuousAt (fun q : E × E => (f q).1) 0 :=
      continuous_fst.continuousAt.comp (hf.continuous.continuousAt)
    have ht : Tendsto (fun q : E × E => (f q).1) (𝓝 0) (𝓝 x) := by
      have ht' := hc.tendsto
      change Tendsto (fun q : E × E => (f q).1) (𝓝 0) (𝓝 ((f 0).1)) at ht'
      rw [hf₀] at ht'
      exact ht' 
    exact hREq.comp_tendsto ht
  refine ⟨hRJ.congr_germ hRrep,?_⟩
  have haJ : LocalSmoothJetBudget (a ∘ f) 0 N A :=
    (hComp r hr x hx hp hr₁ β hβ hLj z (actualFramedCoefficientRadialRemainder d) A₀
      (hRemainder x hx z (closedBall_subset_closedBall (by norm_num) hz)).1).enlarge (le_max_right _ _)
  have hzJ : LocalSmoothJetBudget (fun q : E × E => z+q.2) 0 N 1 := by
    let J := ContinuousLinearMap.snd ℝ E E
    have hJ : ‖J‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      rw [one_mul]
      exact norm_snd_le v
    refine ⟨contDiffAt_const.add contDiff_snd.contDiffAt,?_⟩
    intro n hn
    by_cases h : n=0
    · subst n; simpa only [norm_iteratedFDeriv_zero,Prod.snd_zero,add_zero] using mem_closedBall_zero_iff.mp hz
    · exact (norm_iteratedFDeriv_affine_pos_le J z 0 n (by omega)).trans hJ
  have hIn := (haJ.prod hzJ).enlarge (max_eq_left hA).le
  have hQJ : LocalSmoothJetBudget (fun q => Q (a (f q),z+q.2)) 0 N B := by
    change LocalSmoothJetBudget (Q ∘ (fun q : E × E => (a (f q),z+q.2))) 0 N B
    apply hIn.comp _ hA
    exact ⟨hQ.contDiffAt,hQB _ ⟨mem_closedBall_zero_iff.mpr haJ.value_norm_le,
      by simpa only [Prod.snd_zero,add_zero] using hz⟩⟩
  let J₀ : E × E →L[ℝ] FramedRadialParameter dim :=
    ((β⁻¹ • K₁).prod (0 : E × E →L[ℝ] ℝ)).prod (ContinuousLinearMap.snd ℝ E E)
  have hJ₀ : ‖J₀‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    rw [one_mul]
    change ‖((β⁻¹ • v.1,(0:ℝ)),v.2)‖ ≤ ‖v‖
    rw [Prod.norm_def,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _),norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hβ))]
    exact max_le ((mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hβ)).trans (norm_fst_le _))
      (norm_snd_le v)
  let I₀ (q : E × E) := ((x,0),z)+J₀ q
  have hI₀ : I₀ 0 = ((x,0),z) := by simp [I₀]
  obtain ⟨hF₁,_⟩ := hA₁ floor hFloor ε hε (hs.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd hFrame
  have hAJ := (hF₁ x hx z (closedBall_subset_closedBall (by norm_num) hz)).1
  have hCompL := LocalSmoothJetBudget.comp_of_positive_inner
    (contDiffAt_const.add J₀.contDiff.contDiffAt) (hI₀.symm ▸ hAJ) le_rfl
    (fun n hn _ => (norm_iteratedFDeriv_affine_pos_le J₀ ((x,0),z) 0 n hn).trans hJ₀)
  have hLJ : LocalSmoothJetBudget (l ∘ f) 0 N L₁ := by
    have h := hCompL.linear_postcomp (matrixEntryL (0:I dim) 0)
    have hEq : (matrixEntryL (0:I dim) 0) ∘ actualRelativeCoefficientFirst d ∘ I₀ = l ∘ f := by
      funext q
      have he : I₀ q = ((x+β⁻¹ • q.1,0),z+q.2) := by
        change ((x+β⁻¹ • q.1,(0:ℝ)+0),z+q.2) = _
        rw [add_zero]
      simp [Function.comp_apply,he,f,l,actualRelativeCoefficientFirst,actualFramedCoefficientFirst,matrixEntryL]
    rw [hEq] at h
    simpa only [L₁,one_pow,mul_one] using h
  have hPJ := hLJ.add (hRJ.real_mul hQJ)
  have hVp : f 0 ∈ V₁ := by rw [hf₀]; exact hSV₁ ⟨mem_singleton _,hz⟩
  have hVl : f 0 ∈ V₂ := by rw [hf₀]; exact hSV₂ ⟨mem_singleton _,hz⟩
  have hEP : P ∘ f =ᶠ[𝓝 0] p ∘ f := by
    filter_upwards [hf.continuous.continuousAt.eventually (hV₁.mem_nhds hVp)] with q hq
    exact hPEq hq
  have hEL : L ∘ f =ᶠ[𝓝 0] l ∘ f := by
    filter_upwards [hf.continuous.continuousAt.eventually (hV₂.mem_nhds hVl)] with q hq
    exact hLEq hq
  have hVq : f 0 ∈ V₃ := by rw [hf₀]; exact hSV₃ ⟨mem_singleton _,hz⟩
  have hEQ₂ : Q₂ ∘ f =ᶠ[𝓝 0] q₂ ∘ f := by
    filter_upwards [hf.continuous.continuousAt.eventually (hV₃.mem_nhds hVq)] with q hq
    exact hQ₂Eq hq
  have hDP : L₁+(2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖*C*B ≤ D := by dsimp only [D]; first | exact le_add_of_nonneg_right hB | exact le_add_of_nonneg_left (by positivity)
  have hDL : L₁ ≤ D := by
    dsimp only [D]
    exact (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right hB)
  have hDQ : B ≤ D := by dsimp only [D]; first | exact le_add_of_nonneg_right hB | exact le_add_of_nonneg_left (by positivity)
  exact ⟨(hPJ.enlarge hDP).congr_germ hEP,(hLJ.enlarge hDL).congr_germ hEL,
    (hQJ.enlarge hDQ).congr_germ hEQ₂⟩

theorem uniform_actual_radialNumerator_germs (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (N : ℕ) (hN : N ≤ 8) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C D : ℝ, 0 < η ∧ 0 ≤ C ∧ 0 ≤ D ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ x ∈ Y,∃ (R : X dim → ℝ) (P L : X dim × X dim → ℝ) (V : Set (X dim × X dim)),
        ContDiff ℝ ∞ R ∧ R =ᶠ[𝓝 x] d.radius ∧ ContDiff ℝ ∞ P ∧ ContDiff ℝ ∞ L ∧
        IsOpen V ∧ ({x} ×ˢ closedBall (0:X dim) 1) ⊆ V ∧
        (∀ y z,(y,z) ∈ V → y ∈ Y → z ∈ standardSphere dim →
          L (y,z) = firstDensityCenterLinear d y z ∧
          conormalWeightQuadratic (actualFramedCoefficientField d ((y,d.radius y),z)) z =
            1+d.radius y*P (y,z)) ∧
        ∀ z ∈ closedBall (0:X dim) 1,
          let β := beta d.γ d.radius x
          LocalSmoothJetBudget (fun q : X dim × X dim => R (x+β⁻¹ • q.1)) 0 N C ∧
          LocalSmoothJetBudget (fun q : X dim × X dim => P (x+β⁻¹ • q.1,z+q.2)) 0 N D ∧
          LocalSmoothJetBudget (fun q : X dim × X dim => L (x+β⁻¹ • q.1,z+q.2)) 0 N D := by
  obtain ⟨η,C,D,hη,hC,hD,h⟩ :=
    uniform_actual_radialNumerator_factorization_germs hn hY hΩ hYc hSub N hN hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,D,hη,hC,hD,?_⟩
  intro floor hf ε hε hs d hd hFrame x hx
  obtain ⟨R,P,L,_,V,hR,hREq,hP,hL,_,hV,hBall,hEq,hJet⟩ := h floor hf ε hε hs d hd hFrame x hx
  refine ⟨R,P,L,V,hR,hREq,hP,hL,hV,hBall,?_,?_⟩
  · intro y z hy₀ hy hz
    exact ⟨(hEq y z hy₀ hy hz).1,(hEq y z hy₀ hy hz).2.1⟩
  · intro z hz
    exact ⟨(hJet z hz).1,(hJet z hz).2.1,(hJet z hz).2.2.1⟩

end CalderonN
