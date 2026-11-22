/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.CompactSupport
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Density
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Extension

/-! From Proof/TauCeti/Analysis/Sobolev/W1p/CompactSupport.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 





















































public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology

open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {K : Set E}

 

 





theorem W1p.mem_w1p0Submodule_of_isCompact (hp : p ≠ (∞ : ℝ≥0∞)) {u : W1p mu Omega p}
    (hK : IsCompact K) (hKO : K ⊆ (Omega : Set E))
    (hu : ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K → W1p.value u x = 0) :
    u ∈ w1p0Submodule mu Omega p := by
  have hmeas : MeasurableSet (Omega : Set E) := Omega.isOpen.measurableSet
  have hsub : (Omega : Set E) ⊆ ((⊤ : Opens E) : Set E) := by simp
  have humu : ∀ᵐ x ∂mu, x ∈ (Omega : Set E) → x ∉ K → W1p.value u x = 0 :=
    (ae_restrict_iff' hmeas).1 hu
   
  have hgrad : ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K → W1p.gradient u x = 0 := by
    set V : Opens E := ⟨(Omega : Set E) \ K, Omega.isOpen.sdiff hK.isClosed⟩
    have hVmeas : MeasurableSet (V : Set E) := V.isOpen.measurableSet
    have hvalV : ∀ᵐ x ∂mu.restrict (V : Set E), W1p.value u x = 0 := by
      rw [ae_restrict_iff' hVmeas]
      filter_upwards [humu] with x hx hxV
      exact hx hxV.1 hxV.2
    have hgradV := (ae_restrict_iff' hVmeas).1
      (W1p.gradient_ae_eq_zero_of_value_ae_eq_zero (V := V) Set.sdiff_subset hvalV)
    rw [ae_restrict_iff' hmeas]
    filter_upwards [hgradV] with x hx hxO hxK
    exact hx ⟨hxO, hxK⟩
   
  have hweak : HasWeakFDerivOn mu ⊤
      ((extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.value u) : E → ℝ))
      (fun x => innerSL ℝ (extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.gradient u) x)) := by
    have hU : ∀ᵐ x ∂mu.restrict (Omega : Set E), x ∉ K →
        innerSL ℝ (W1p.gradient u x) = 0 := by
      filter_upwards [hgrad] with x hx hxK
      rw [hx hxK, map_zero]
    refine (((W1p.hasWeakFDerivOn u).indicator_of_isCompact hK hKO hu hU).congr_ae
      (coeFn_extendByZeroLpₗᵢ ℝ hmeas hsub (W1p.value u)).symm).congr_ae_deriv ?_
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hmeas hsub (W1p.gradient u)] with x hx
    rw [hx]
    by_cases hxO : x ∈ (Omega : Set E) <;> simp [hxO]
  set w : W1p mu (⊤ : Opens E) p :=
    W1p.mk (extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.value u))
      (extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.gradient u)) hweak with hwdef
  have hvalw : ⇑(W1p.value w) =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)]
      (Omega : Set E).indicator (W1p.value u : E → ℝ) := by
    rw [hwdef, W1p.value_mk]
    exact coeFn_extendByZeroLpₗᵢ ℝ hmeas hsub (W1p.value u)
   
  obtain ⟨chi, M, hchi, -, hchi_one_nhds, hchi_cpt, hchi_ts, hM0, hchiM_all,
    hchigradM_all⟩ := hK.exists_contDiff_cutoff_with_bounds Omega.isOpen hKO
  have hchi_one : ∀ x ∈ K, chi x = 1 := fun x hx => by
    have hx' : x ∈ chi ⁻¹' ({1} : Set ℝ) := interior_subset (hchi_one_nhds hx)
    exact hx'
  have hchiM : ∀ x ∈ ((⊤ : Opens E) : Set E), |chi x| ≤ M := fun x _ => hchiM_all x
  have hchigradM : ∀ x ∈ ((⊤ : Opens E) : Set E), ‖∇ chi x‖ ≤ M :=
    fun x _ => hchigradM_all x
   
  have hLw : W1p.contDiffSMul chi hchi hM0 hchiM hchigradM w = w := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hchi hM0 hchiM hchigradM w, hvalw,
      humu.filter_mono (ae_mono Measure.restrict_le_self)] with x h1 h2 h3
    rw [h1]
    by_cases hxK : x ∈ K
    · rw [hchi_one x hxK]
      simp
    · have hzero : W1p.value w x = 0 := by
        rw [h2]
        by_cases hxO : x ∈ (Omega : Set E)
        · rw [indicator_of_mem hxO, h3 hxO hxK]
        · rw [indicator_of_notMem hxO]
      rw [hzero, smul_zero]
   
  have hcomplete : CompleteSpace (W1p0 mu Omega p) :=
    (w1p0Submodule mu Omega p).isClosed.completeSpace_coe
  set F : W1p0 mu Omega p →L[ℝ] W1p mu (⊤ : Opens E) p :=
    (w1p0Submodule mu (⊤ : Opens E) p).toSubmodule.subtypeL.comp
      (W1p0.extendByZeroL (le_top : Omega ≤ ⊤)) with hFdef
  have hFiso : Isometry F :=
    AddMonoidHomClass.isometry_of_norm F fun z => W1p0.norm_extendByZeroL le_top z
  have hclosed : IsClosed (Set.range F) := hFiso.isClosedEmbedding.isClosed_range
   
  have htest : ∀ phi : 𝓓((⊤ : Opens E), ℝ),
      W1p.ofTestFunctionₗ mu (⊤ : Opens E) p phi ∈
        W1p.contDiffSMulL chi hchi hM0 hchiM hchigradM ⁻¹' Set.range F := by
    intro phi
    obtain ⟨Psi, hPsi⟩ : ∃ Psi : 𝓓(Omega, ℝ), (Psi : E → ℝ) = chi * (phi : E → ℝ) :=
      ⟨⟨chi * (phi : E → ℝ), hchi.mul phi.contDiff, hchi_cpt.mul_right,
        tsupport_mul_subset_left.trans hchi_ts⟩, rfl⟩
    have hcoe : ((TestFunction.monoCLM ℝ Psi : 𝓓((⊤ : Opens E), ℝ)) : E → ℝ)
        = chi * (phi : E → ℝ) := by
      rw [TestFunction.monoCLM_apply, ← hPsi]
      simp
    refine ⟨⟨W1p.ofTestFunctionₗ mu Omega p Psi, W1p.ofTestFunctionₗ_mem_w1p0Submodule Psi⟩, ?_⟩
    rw [W1p.contDiffSMulL_apply,
      W1p.contDiffSMul_ofTestFunctionₗ hchi hM0 hchiM hchigradM phi
        (TestFunction.monoCLM ℝ Psi) hcoe]
    refine Subtype.ext ?_
    rw [hFdef]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtypeL,
      Submodule.coe_subtype]
    rw [W1p0.coe_extendByZeroL]
    exact Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ le_top Psi
   
  have hwmem : w ∈ Set.range F := by
    have hmem := w1p0Submodule_subset_of_isClosed
      (hclosed.preimage (W1p.contDiffSMulL chi hchi hM0 hchiM hchigradM).continuous) htest
      (W1p.mem_w1p0Submodule_top hp w)
    rw [Set.mem_preimage, W1p.contDiffSMulL_apply, hLw] at hmem
    exact hmem
  obtain ⟨z, hz⟩ := hwmem
  have hvalz : W1p.value (z : W1p mu Omega p) = W1p.value u := by
    have h1 : W1p.value (F z) =
        extendByZeroLpₗᵢ ℝ mu hmeas hsub (W1p.value (z : W1p mu Omega p)) :=
      W1p0.value_extendByZeroL le_top z
    rw [hz, hwdef, W1p.value_mk] at h1
    exact (extendByZeroLpₗᵢ ℝ mu hmeas hsub).injective h1.symm
  exact W1p.ext_value hvalz ▸ z.2

 

 



theorem W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (hp : p ≠ (∞ : ℝ≥0∞))
    {psi : E → ℝ}
    (hpsi : ContDiff ℝ ∞ psi) {M : ℝ} (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M)
    (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M) (hcpt : HasCompactSupport psi)
    (hts : tsupport psi ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1p0Submodule mu Omega p := by
  refine W1p.mem_w1p0Submodule_of_isCompact hp hcpt hts ?_
  filter_upwards [W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM u] with x hx hxK
  rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_smul]

 

 


theorem W1p.value_extendByZeroL_contDiffSMul_ae {psi : E → ℝ} (hpsi : ContDiff ℝ ∞ psi) {M : ℝ}
    (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M) (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M)
    (u : W1p mu Omega p)
    (hw : W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1p0Submodule mu Omega p) :
    ∀ᵐ x ∂mu, W1p.value (W1p0.extendByZeroL le_top ⟨_, hw⟩ : W1p mu ⊤ p) x =
      (Omega : Set E).indicator (fun y => psi y * W1p.value u y) x := by
  have hOmega := Omega.isOpen.measurableSet
  have h2 := (coeFn_extendByZeroLpₗᵢ ℝ (μ := mu) hOmega
    (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤))
    (W1p.value (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u))).filter_mono
      (ae_mono (by rw [Opens.coe_top, Measure.restrict_univ]))
  have h3 := (ae_restrict_iff' hOmega).1 (W1p.value_contDiffSMul_ae hpsi hM hpsiM hgradM u)
  filter_upwards [h2, h3] with x hx2 hx3
  rw [W1p0.value_extendByZeroL, hx2]
  by_cases hxO : x ∈ (Omega : Set E)
  · rw [indicator_of_mem hxO, indicator_of_mem hxO, hx3 hxO, smul_eq_mul]
  · rw [indicator_of_notMem hxO, indicator_of_notMem hxO]

 


theorem W1p.gradient_extendByZeroL_contDiffSMul_ae {psi : E → ℝ} (hpsi : ContDiff ℝ ∞ psi)
    {M : ℝ} (hM : 0 ≤ M) (hpsiM : ∀ x ∈ Omega, |psi x| ≤ M)
    (hgradM : ∀ x ∈ Omega, ‖∇ psi x‖ ≤ M) (u : W1p mu Omega p)
    (hw : W1p.contDiffSMul psi hpsi hM hpsiM hgradM u ∈ w1p0Submodule mu Omega p) :
    ∀ᵐ x ∂mu, W1p.gradient (W1p0.extendByZeroL le_top ⟨_, hw⟩ : W1p mu ⊤ p) x =
      (Omega : Set E).indicator
        (fun y => psi y • W1p.gradient u y + W1p.value u y • ∇ psi y) x := by
  have hOmega := Omega.isOpen.measurableSet
  have h2 := (coeFn_extendByZeroLpₗᵢ ℝ (μ := mu) hOmega
    (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤))
    (W1p.gradient (W1p.contDiffSMul psi hpsi hM hpsiM hgradM u))).filter_mono
      (ae_mono (by rw [Opens.coe_top, Measure.restrict_univ]))
  have h3 := (ae_restrict_iff' hOmega).1 (W1p.gradient_contDiffSMul_ae hpsi hM hpsiM hgradM u)
  filter_upwards [h2, h3] with x hx2 hx3
  rw [W1p0.gradient_extendByZeroL, hx2]
  by_cases hxO : x ∈ (Omega : Set E)
  · rw [indicator_of_mem hxO, indicator_of_mem hxO, hx3 hxO]
  · rw [indicator_of_notMem hxO, indicator_of_notMem hxO]

 



theorem W1p.exists_top_value_gradient_ae_eq_on_of_isCompact (hp : p ≠ (∞ : ENNReal))
    (u : W1p mu Omega p) {S : Set E}
    (hS : IsCompact S) (hSO : S ⊆ Omega) :
    ∃ w : W1p mu ⊤ p, (∀ᵐ x ∂mu, x ∈ S → W1p.value w x = W1p.value u x) ∧
      ∀ᵐ x ∂mu, x ∈ S → W1p.gradient w x = W1p.gradient u x := by
   
  obtain ⟨chi, M, hchi, -, hchi_one, hchi_cpt, hchi_ts, hM0, hchiM_all, hchigradM_all⟩ :=
    hS.exists_contDiff_cutoff_with_bounds Omega.isOpen hSO
  have hchiM : ∀ x ∈ (Omega : Set E), |chi x| ≤ M := fun x _ => hchiM_all x
  have hchigradM : ∀ x ∈ (Omega : Set E), ‖∇ chi x‖ ≤ M := fun x _ => hchigradM_all x
   
  have hchi_S : ∀ x ∈ S, chi x = 1 ∧ ∇ chi x = 0 := fun x hx => by
    have hev : chi =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 (hchi_one hx)) fun y hy => hy
    refine ⟨hev.eq_of_nhds, ?_⟩
    rw [_root_.gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]
   
  have hw0 := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport hp hchi hM0 hchiM
    hchigradM hchi_cpt hchi_ts u
  refine ⟨(W1p0.extendByZeroL (p := p) (Omega := Omega) le_top ⟨_, hw0⟩).1, ?_, ?_⟩
  · filter_upwards [W1p.value_extendByZeroL_contDiffSMul_ae hchi hM0 hchiM hchigradM u hw0]
      with x hx hxS
    rw [hx, indicator_of_mem (hSO hxS), (hchi_S x hxS).1, one_mul]
  · filter_upwards [W1p.gradient_extendByZeroL_contDiffSMul_ae hchi hM0 hchiM hchigradM u hw0]
      with x hx hxS
    rw [hx, indicator_of_mem (hSO hxS), (hchi_S x hxS).1, (hchi_S x hxS).2, one_smul,
      smul_zero, add_zero]

end TauCeti
