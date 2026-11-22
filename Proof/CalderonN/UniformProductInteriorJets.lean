module

public import Proof.CalderonN.ProductDerivativeWords
public import Proof.CalderonN.ClassicalInteriorJets
public import Proof.CalderonN.GreenCross

import Proof.CalderonN.CrossTensor

import Mathlib.Tactic

public section

set_option maxHeartbeats 2600000

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {d : ℕ} [NeZero d]
open LocalMetricExtension (integral_sq_eq_norm_sq)

private theorem exists_uniform_harmonic_jet_bound_of_sup
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {J : Set P} (hJ : IsCompact J)
    {U K : Set (X d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hK : IsCompact K) (hKU : K ⊆ U) {g : P → (MetricField d)}
    (hg : ∀ p ∈ J, SmoothMetric U (g p))
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun q : P × (X d) => divergenceCoeff (g q.1) q.2 i j) (univ ×ˢ U))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ f : (X d) → ℝ, Harmonic U (g p) f →
      ∀ M : ℝ, 0 ≤ M → (∀ z ∈ U, |f z| ≤ M) →
      ∀ k ≤ n, ∀ z ∈ K, ‖iteratedFDeriv ℝ k f z‖ ≤ C*M := by
  choose C hC hJet using (fun k : Fin (n+1) =>
    exists_uniform_harmonic_interior_jet_bound hJ hU hg ha hK hKU k.val)
  let S := ∑ j, C j
  let μ := (volume : Measure (X d)).restrict U
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => hC j)
  let V := Real.sqrt (μ.real univ)
  have hV : 0 ≤ V := Real.sqrt_nonneg _
  have hfin : (volume : Measure (X d)) U ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hUc.measure_lt_top).ne
  let _ : IsFiniteMeasure ((volume : Measure (X d)).restrict U) := isFiniteMeasure_restrict.mpr hfin
  refine ⟨S*V,mul_nonneg hS hV,?_⟩
  intro p hp f hf M hM hBound k hk z hz
  have hMeas : AEStronglyMeasurable f μ := hf.1.continuousOn.aestronglyMeasurable hU.measurableSet
  have hAE : ∀ᵐ x ∂μ, ‖f x‖ ≤ M :=
    ae_restrict_of_forall_mem hU.measurableSet (fun x hx => by simpa only [Real.norm_eq_abs] using hBound x hx)
  have hLp : MemLp f 2 μ := MemLp.of_bound hMeas M hAE
  let u := hLp.toLp f
  have hu : (u : (X d) → ℝ) =ᵐ[μ] f := MemLp.coeFn_toLp hLp
  have huB : ‖u‖ ≤ V*M := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hV hM)).mp
    calc
      ‖u‖^2 = ∫ x, (u x)^2 ∂μ := (integral_sq_eq_norm_sq u).symm
      _ = ∫ x, (f x)^2 ∂μ := integral_congr_ae (hu.mono fun x hx => congrArg (fun p : ℝ => p^2) hx)
      _ ≤ ∫ _, M^2 ∂μ := integral_mono_ae hLp.integrable_sq (integrable_const _)
        (hAE.mono fun x hx => by
          simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg (f x)) hx 2))
      _ = (V*M)^2 := by
        rw [integral_const,smul_eq_mul,mul_pow]
        dsimp only [V]
        rw [Real.sq_sqrt (measureReal_nonneg : 0 ≤ μ.real univ)]
  let j : Fin (n+1) := ⟨k,by omega⟩
  have hCS : C j ≤ S := Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ j)
  calc
    ‖iteratedFDeriv ℝ k f z‖ ≤ C j * ‖u‖ := hJet j p hp u f hf hu z hz
    _ ≤ S*(V*M) := mul_le_mul hCS huB (norm_nonneg _) hS
    _ = _ := by ring

private def selectedComponent (v : Bool × ((X d) × (X d))) : (X d) × (X d) :=
  if v.1 then (v.2.1,0) else (0,v.2.2)

private theorem exists_split_word (w : List (Bool × ((X d) × (X d))))
    (hUnit : ∀ v ∈ w, ‖v.2‖ ≤ 1) :
    ∃ l r : List (X d), l.length+r.length = w.length ∧
      (∀ a ∈ l, ‖a‖ ≤ 1) ∧ (∀ b ∈ r, ‖b‖ ≤ 1) ∧
      (w.map selectedComponent).Perm
        (l.map (fun v => (v,0)) ++ r.map (fun v => (0,v))) := by
  induction w with
  | nil => exact ⟨[],[],rfl,by simp,by simp,List.Perm.nil⟩
  | cons v w ih =>
    obtain ⟨l,r,hLen,hl,hr,hPerm⟩ := ih (fun v hv => hUnit v (List.mem_cons_of_mem _ hv))
    have hv := hUnit v (List.mem_cons_self)
    rcases v with ⟨b,x,y⟩
    cases b
    · refine ⟨l,y::r,by simp only [List.length_cons]; omega,hl,?_,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact (norm_snd_le (x,z)).trans hv
        · exact hr z hz
      · simp only [List.map_cons,selectedComponent,Bool.false_eq_true,ite_false]
        exact (hPerm.cons (0,y)).trans List.perm_middle.symm
    · refine ⟨x::l,r,by simp only [List.length_cons]; omega,?_,hr,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact (norm_fst_le (z,y)).trans hv
        · exact hl z hz
      · simpa only [List.map_cons,selectedComponent,ite_true,List.cons_append] using hPerm.cons (x,0)

private theorem opNorm_le_of_unit_product_dirs {k : ℕ}
    (L : ((X d) × (X d)) [×k]→L[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v : Fin k → (X d) × (X d), (∀ i, ‖v i‖ ≤ 1) → ‖L v‖ ≤ C) : ‖L‖ ≤ C := by
  apply L.opNorm_le_bound hC
  intro v
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i,hi⟩ := hz
    rw [L.map_coord_zero i hi,norm_zero]
    positivity
  · push Not at hz
    let w (i : Fin k) := (‖v i‖)⁻¹ • v i
    have hnorm (i : Fin k) : ‖w i‖ = 1 := by
      rw [norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hz i))]
    have he : v = fun i => ‖v i‖ • w i := by
      funext i
      exact (smul_inv_smul₀ (norm_ne_zero_iff.mpr (hz i)) _).symm
    calc
      ‖L v‖ = ‖L (fun i => ‖v i‖ • w i)‖ := congrArg (fun z => ‖L z‖) he
      _ = (∏ i, ‖v i‖)*‖L w‖ := by
        rw [L.map_smul_univ,norm_smul,Real.norm_eq_abs,
          abs_of_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))]
      _ ≤ (∏ i, ‖v i‖)*C := mul_le_mul_of_nonneg_left (h w (fun i => (hnorm i).le))
        (Finset.prod_nonneg (fun i _ => norm_nonneg (v i)))
      _ = _ := mul_comm _ _

/-- All joint derivatives of bounded two-variable harmonic data are
uniformly controlled on compact rectangles for a compact metric family. -/
theorem exists_uniform_product_interior_jet_bound_of_sup
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {J : Set P} (hJ : IsCompact J)
    {U V K L : Set (X d)} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsCompact (closure U)) (hVc : IsCompact (closure V))
    (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    {g₁ g₂ : P → (MetricField d)}
    (hg₁ : ∀ p ∈ J, SmoothMetric U (g₁ p))
    (hg₂ : ∀ p ∈ J, SmoothMetric V (g₂ p))
    (ha₁ : ∀ i j, ContDiffOn ℝ ∞ (fun q : P × (X d) => divergenceCoeff (g₁ q.1) q.2 i j) (univ ×ˢ U))
    (ha₂ : ∀ i j, ContDiffOn ℝ ∞ (fun q : P × (X d) => divergenceCoeff (g₂ q.1) q.2 i j) (univ ×ˢ V))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ f : (X d) × (X d) → ℝ, ContDiff ℝ ∞ f →
      ProductSolutionOn (g₁ p) (g₂ p) (U ×ˢ V) f → ∀ M : ℝ, 0 ≤ M →
      (∀ q ∈ U ×ˢ V, |f q| ≤ M) →
      ∀ k ≤ n, ∀ q ∈ K ×ˢ L, ‖iteratedFDeriv ℝ k f q‖ ≤ C*M := by
  obtain ⟨A,hA,hLeft⟩ := exists_uniform_harmonic_jet_bound_of_sup hJ hU hUc hK hKU hg₁ ha₁ n
  obtain ⟨B,hB,hRight⟩ := exists_uniform_harmonic_jet_bound_of_sup hJ hV hVc hL hLV hg₂ ha₂ n
  let C := (2 : ℝ)^n*(A*B)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp f hf hLap M hM hBound k hk q hq
  have hR (w : List (X d)) (hw : w.length ≤ n) (hW : ∀ v ∈ w, ‖v‖ ≤ 1) (x : (X d)) (hx : x ∈ U) :
      |directionalWord (w.map (fun v => (0,v))) f (x,q.2)| ≤ B*M := by
    let f' (y : (X d)) := f (x,y)
    have hf' : ContDiff ℝ ∞ f' := hf.comp (contDiff_const.prodMk contDiff_id)
    have hH : Harmonic V (g₂ p) f' := ⟨hf'.contDiffOn,fun y hy => hLap.2.2 (x,y) ⟨hx,hy⟩⟩
    rw [← show directionalWord w f' q.2 = _ from congrFun (directionalWord_productSlice_right hf w x) q.2]
    exact (abs_directionalWord_le_iteratedFDeriv_of_unit hf' w q.2 hW).trans
      (hRight p hp f' hH M hM (fun y hy => hBound (x,y) ⟨hx,hy⟩) _ hw q.2 hq.2)
  have hW (l r : List (X d)) (hl : l.length ≤ n) (hr : r.length ≤ n)
      (hLU : ∀ x ∈ l, ‖x‖ ≤ 1) (hRU : ∀ x ∈ r, ‖x‖ ≤ 1) :
      |directionalWord (l.map (fun v => (v,0)) ++ r.map (fun v => (0,v))) f q| ≤ A*(B*M) := by
    let F := directionalWord (r.map (fun v => (0,v))) f
    have hF := contDiff_directionalWord hf (r.map (fun v => ((0 : (X d)),v)))
    let F' (x : (X d)) := F (x,q.2)
    have hF' : ContDiff ℝ ∞ F' := hF.comp (contDiff_id.prodMk contDiff_const)
    have hH : Harmonic U (g₁ p) F' :=
      harmonic_left_directionalWord_right hf hV hLap.2.1 r q.2 (hLV hq.2)
    rw [directionalWord_append]
    change |directionalWord (l.map (fun v => (v,0))) F (q.1,q.2)| ≤ _
    rw [← show directionalWord l F' q.1 = _ from congrFun (directionalWord_productSlice_left hF l q.2) q.1]
    exact (abs_directionalWord_le_iteratedFDeriv_of_unit hF' l q.1 hLU).trans
      (hLeft p hp F' hH (B*M) (mul_nonneg hB hM) (hR r hr hRU) _ hl q.1 hq.1)
  apply opNorm_le_of_unit_product_dirs _ (mul_nonneg hC hM)
  intro v hv
  let L₀ := iteratedFDeriv ℝ k f q
  let E (c : Bool) (i : Fin k) : (X d) × (X d) := selectedComponent (c,v i)
  have hsum (i : Fin k) : ∑ c : Bool, E c i = v i := by
    rw [Fintype.sum_bool]
    simp [E, selectedComponent, Prod.add_def]
  have hexpand : L₀ v = ∑ b : Fin k → Bool, L₀ (fun i => E (b i) i) := by
    calc
      L₀ v = L₀ (fun i => ∑ c : Bool, E c i) := congrArg L₀ (funext hsum).symm
      _ = _ := L₀.map_sum _
  have hterm (b : Fin k → Bool) : ‖L₀ (fun i => E (b i) i)‖ ≤ A*(B*M) := by
    let w := List.ofFn (fun i => (b i,v i))
    have hw (z : Bool × ((X d) × (X d))) (hz : z ∈ w) : ‖z.2‖ ≤ 1 := by
      rw [List.mem_ofFn] at hz
      obtain ⟨i,rfl⟩ := hz
      exact hv i
    obtain ⟨l,r,hLen,hl,hr,hPerm⟩ := exists_split_word w hw
    have hLen' : l.length+r.length = k := hLen.trans List.length_ofFn
    change ‖iteratedFDeriv ℝ k f q (fun i => E (b i) i)‖ ≤ _
    rw [← directionalWord_ofFn_eq_iteratedFDeriv hf,Real.norm_eq_abs]
    have he : List.ofFn (fun i => E (b i) i) = w.map selectedComponent := (List.map_ofFn (f := fun i : Fin k => (b i,v i)) (g := selectedComponent)).symm
    rw [he,directionalWord_product_perm hf hPerm]
    exact hW l r (by omega) (by omega) hl hr
  rw [show iteratedFDeriv ℝ k f q v = L₀ v from rfl,hexpand]
  calc
    _ ≤ ∑ b : Fin k → Bool, ‖L₀ (fun i => E (b i) i)‖ := norm_sum_le _ _
    _ ≤ ∑ _b : Fin k → Bool, A*(B*M) := Finset.sum_le_sum (fun b _ => hterm b)
    _ = (2 : ℝ)^k*(A*(B*M)) := by simp
    _ ≤ C*M := by
      rw [show C*M = (2:ℝ)^n*(A*(B*M)) by dsimp only [C]; ring]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk)
        (mul_nonneg hA (mul_nonneg hB hM))

end CalderonN
