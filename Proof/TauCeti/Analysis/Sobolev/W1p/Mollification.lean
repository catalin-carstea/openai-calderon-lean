/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.Translation
public import Proof.TauCeti.Analysis.Sobolev.W1p.Zero
public import Proof.TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
public import Proof.TauCeti.MeasureTheory.Function.Lp.MollificationBridge

 





































public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Convolution Distributions ENNReal Topology

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

 
local instance : (mu.restrict ((⊤ : Opens E) : Set E)).IsAddHaarMeasure := by
  rw [Opens.coe_top, Measure.restrict_univ]
  infer_instance

 

theorem Sobolev1JetLp.normedBumpLp_mem_w1pSubmodule (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    {J : Sobolev1JetLp mu ⊤ p} (hJ : J ∈ w1pSubmodule mu ⊤ p) :
    normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) J ∈ w1pSubmodule mu ⊤ p := by
  set nu := mu.restrict ((⊤ : Opens E) : Set E)
  let S := (w1pSubmodule mu ⊤ p).toSubmodule
  let g : E → S := fun t =>
    ⟨phi.normed nu t • nu.translateLp p (-t) J,
      S.smul_mem _ (Sobolev1JetLp.translateLp_mem_w1pSubmodule (-t) hJ)⟩
  have hint : normedBumpLp hp phi nu J = S.subtypeₗᵢ (∫ t, g t ∂nu) := by
    rw [← LinearIsometry.integral_comp_comm, normedBumpLp_apply]
    simp only [g, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype]
  rw [hint]
  exact (∫ t, g t ∂nu).2

 


def W1p.normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    W1p mu ⊤ p →L[ℝ] W1p mu ⊤ p :=
  ContinuousLinearMap.codRestrict
    ((normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E))).comp
      (w1pSubmodule mu ⊤ p).toSubmodule.subtypeL)
    (w1pSubmodule mu ⊤ p).toSubmodule
    fun u => Sobolev1JetLp.normedBumpLp_mem_w1pSubmodule hp phi u.2

 
theorem W1p.coe_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (u : W1p mu ⊤ p) :
    ((W1p.normedBumpL hp phi u : W1p mu ⊤ p) : Sobolev1JetLp mu ⊤ p) =
      normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) (u : Sobolev1JetLp mu ⊤ p) :=
  (rfl)

 

theorem Sobolev1JetLp.value_normedBumpLp (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (J : Sobolev1JetLp mu ⊤ p) :
    Sobolev1JetLp.value (normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) J) =
      normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) (Sobolev1JetLp.value J) := by
  rw [← Sobolev1JetLp.valueL_apply, ← Sobolev1JetLp.valueL_apply,
    Sobolev1JetLp.valueL_eq_compLpL]
  exact compLpL_normedBumpLp hp phi _ J

 

theorem Sobolev1JetLp.gradient_normedBumpLp (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    (J : Sobolev1JetLp mu ⊤ p) :
    Sobolev1JetLp.gradient (normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) J) =
      normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) (Sobolev1JetLp.gradient J) := by
  rw [← Sobolev1JetLp.gradientL_apply, ← Sobolev1JetLp.gradientL_apply,
    Sobolev1JetLp.gradientL_eq_compLpL]
  exact compLpL_normedBumpLp hp phi _ J

 
theorem W1p.value_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (u : W1p mu ⊤ p) :
    W1p.value (W1p.normedBumpL hp phi u) =
      normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) (W1p.value u) := by
  rw [W1p.value_coe, W1p.coe_normedBumpL, Sobolev1JetLp.value_normedBumpLp, W1p.value_coe]

 

theorem W1p.gradient_normedBumpL (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) (u : W1p mu ⊤ p) :
    W1p.gradient (W1p.normedBumpL hp phi u) =
      normedBumpLp hp phi (mu.restrict ((⊤ : Opens E) : Set E)) (W1p.gradient u) := by
  rw [W1p.gradient_coe, W1p.coe_normedBumpL, Sobolev1JetLp.gradient_normedBumpLp,
    W1p.gradient_coe]

 

theorem W1p.norm_normedBumpL_le_one (hp : p ≠ ∞) (phi : ContDiffBump (0 : E)) :
    ‖W1p.normedBumpL (mu := mu) hp phi‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [← Submodule.norm_coe, W1p.coe_normedBumpL, ← Submodule.norm_coe u]
  exact ContinuousLinearMap.le_of_opNorm_le _ (norm_normedBumpLp_le_one hp phi) _

 


theorem W1p.tendsto_normedBumpL (hp : p ≠ ∞) {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)} (hphi : Tendsto (fun i => (phi i).rOut) l (𝓝 0))
    (u : W1p mu ⊤ p) :
    Tendsto (fun i => W1p.normedBumpL hp (phi i) u) l (𝓝 u) := by
  rw [tendsto_subtype_rng]
  exact tendsto_normedBumpLp hp hphi (u : Sobolev1JetLp mu ⊤ p)

 


theorem W1p.normedBumpL_mem_range_of_ae_eq_zero (hp : p ≠ ∞) (phi : ContDiffBump (0 : E))
    {u : W1p mu ⊤ p} {K : Set E} (hK : IsCompact K)
    (hu : ∀ᵐ x ∂(mu.restrict ((⊤ : Opens E) : Set E)), x ∉ K →
      (u : Sobolev1JetLp mu ⊤ p) x = 0) :
    W1p.normedBumpL hp phi u ∈ LinearMap.range (W1p.ofTestFunctionₗ mu ⊤ p) := by
  set nu := mu.restrict ((⊤ : Opens E) : Set E)
  set J : Sobolev1JetLp mu ⊤ p := u.1 with hJdef
  let Jt : E → Sobolev1Jet E := K.indicator J
  have hJt_mem : MemLp Jt p nu := (Lp.memLp J).indicator hK.measurableSet.nullMeasurableSet
  have hJt_cpt : HasCompactSupport Jt :=
    HasCompactSupport.intro hK fun x hx => indicator_of_notMem hx _
  have hJ_eq : hJt_mem.toLp Jt = J := by
    apply Lp.ext
    filter_upwards [hJt_mem.coeFn_toLp, hu] with x hx hux
    rw [hx]
    by_cases hxK : x ∈ K
    · exact indicator_of_mem hxK _
    · simp only [Jt, indicator_of_notMem hxK, hux hxK]
  let conv : E → Sobolev1Jet E := phi.normed nu ⋆[ContinuousLinearMap.lsmul ℝ ℝ, nu] Jt
  have hbridge : ((W1p.normedBumpL hp phi u : W1p mu ⊤ p) : Sobolev1JetLp mu ⊤ p) =ᵐ[nu] conv := by
    rw [W1p.coe_normedBumpL, ← hJdef, ← hJ_eq]
    exact normedBumpLp_ae_eq_convolution hp phi hJt_mem
  have hconv_smooth : ContDiff ℝ (⊤ : ℕ∞) conv :=
    phi.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      phi.contDiff_normed (hJt_mem.locallyIntegrable Fact.out)
  have hconv_cpt : HasCompactSupport conv :=
    phi.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hJt_cpt
  let Phi : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨fun x => WithLp.fstL 2 ℝ ℝ E (conv x), (WithLp.fstL 2 ℝ ℝ E).contDiff.comp hconv_smooth,
      hconv_cpt.comp_left (map_zero _), subset_univ _⟩
  refine ⟨Phi, W1p.ext_value (Lp.ext ?_)⟩
  rw [W1p.value_ofTestFunctionₗ]
  filter_upwards [testFunctionLp_apply_ae (mu := mu) p Phi,
    W1p.value_apply_ae (W1p.normedBumpL hp phi u), hbridge] with x hPhi hvalue hconv
  rw [hPhi, hvalue, hconv]
  rfl

end TauCeti
