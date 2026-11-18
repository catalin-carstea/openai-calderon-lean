/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.Sobolev.W1p.Zero
public import Proof.TauCeti.MeasureTheory.Function.Lp.ExtendByZero

 



















































public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega Omega' Omega'' : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

 

omit [mu.IsAddHaarMeasure] in
 


def Sobolev1JetLp.extendByZeroₗᵢ (hsub : Omega ≤ Omega') :
    Sobolev1JetLp mu Omega p →ₗᵢ[ℝ] Sobolev1JetLp mu Omega' p :=
  extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
 
theorem Sobolev1JetLp.coeFn_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    (Sobolev1JetLp.extendByZeroₗᵢ hsub J : E → Sobolev1Jet E) =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (J : E → Sobolev1Jet E) :=
  coeFn_extendByZeroLpₗᵢ _ _ _ _

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
 


@[simp]
theorem Sobolev1JetLp.value_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.value (Sobolev1JetLp.extendByZeroₗᵢ hsub J) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Sobolev1JetLp.value J) :=
  (Lp.ext ((coeFn_extendByZeroLpₗᵢ_comp ℝ Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hsub) WithLp.fst rfl (Sobolev1JetLp.value_apply_ae J)).trans
      (Filter.EventuallyEq.symm (Sobolev1JetLp.value_apply_ae _)))).symm

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
 

@[simp]
theorem Sobolev1JetLp.gradient_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.gradient (Sobolev1JetLp.extendByZeroₗᵢ hsub J) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Sobolev1JetLp.gradient J) :=
  (Lp.ext ((coeFn_extendByZeroLpₗᵢ_comp ℝ Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hsub) WithLp.snd rfl (Sobolev1JetLp.gradient_apply_ae J)).trans
      (Filter.EventuallyEq.symm (Sobolev1JetLp.gradient_apply_ae _)))).symm

 

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
 
private theorem coe_monoCLM (hsub : Omega ≤ Omega') (phi : 𝓓(Omega, ℝ)) :
    ((TestFunction.monoCLM ℝ phi : 𝓓(Omega', ℝ)) : E → ℝ) = (phi : E → ℝ) := by
  rw [TestFunction.monoCLM_apply]
  simp [hsub]

omit [FiniteDimensional ℝ E] in
 

private theorem extendByZeroLpₗᵢ_testFunctionLp (hsub : Omega ≤ Omega') (phi : 𝓓(Omega, ℝ)) :
    extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (testFunctionLp p phi) =
      testFunctionLp (mu := mu) (Omega := Omega') p (TestFunction.monoCLM ℝ phi) :=
  extendByZeroLpₗᵢ_eq_of_ae_eq ℝ Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
    ((subset_tsupport _).trans phi.tsupport_subset) (testFunctionLp_apply_ae (mu := mu) p phi) <| by
      filter_upwards [testFunctionLp_apply_ae (mu := mu) (Omega := Omega') p
        (TestFunction.monoCLM ℝ phi)] with x hx
      rw [hx, coe_monoCLM hsub phi]

 

private theorem extendByZeroLpₗᵢ_gradientTestFunctionLp (hsub : Omega ≤ Omega')
    (phi : 𝓓(Omega, ℝ)) :
    extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (gradientTestFunctionLp p phi) =
      gradientTestFunctionLp (mu := mu) (Omega := Omega') p (TestFunction.monoCLM ℝ phi) :=
  extendByZeroLpₗᵢ_eq_of_ae_eq ℝ Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
    (support_gradient_testFunction_subset phi)
    (gradientTestFunctionLp_apply_ae (mu := mu) p phi) <| by
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) (Omega := Omega') p
        (TestFunction.monoCLM ℝ phi)] with x hx
      rw [hx, coe_monoCLM hsub phi]

 

@[simp]
theorem Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ (hsub : Omega ≤ Omega')
    (phi : 𝓓(Omega, ℝ)) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub
        (W1p.ofTestFunctionₗ mu Omega p phi : Sobolev1JetLp mu Omega p) =
      (W1p.ofTestFunctionₗ mu Omega' p (TestFunction.monoCLM ℝ phi) :
        Sobolev1JetLp mu Omega' p) := by
  refine Sobolev1JetLp.ext ?_ ?_
  · rw [Sobolev1JetLp.value_extendByZeroₗᵢ, ← W1p.value_coe, ← W1p.value_coe,
      W1p.value_ofTestFunctionₗ, W1p.value_ofTestFunctionₗ]
    exact extendByZeroLpₗᵢ_testFunctionLp hsub phi
  · rw [Sobolev1JetLp.gradient_extendByZeroₗᵢ, ← W1p.gradient_coe, ← W1p.gradient_coe,
      W1p.gradient_ofTestFunctionₗ, W1p.gradient_ofTestFunctionₗ]
    exact extendByZeroLpₗᵢ_gradientTestFunctionLp hsub phi

 

 

private theorem extendByZero_mem_image (hsub : Omega ≤ Omega') {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p) ∈
      Subtype.val '' (w1p0Submodule mu Omega' p : Set (W1p mu Omega' p)) := by
  have hclosed : IsClosed
      (Subtype.val '' (w1p0Submodule mu Omega' p : Set (W1p mu Omega' p))) :=
    ((w1pSubmodule mu Omega' p).isClosed.isClosedEmbedding_subtypeVal).isClosedMap _
      (w1p0Submodule mu Omega' p).isClosed
  have hcont : Continuous fun v : W1p mu Omega p =>
      Sobolev1JetLp.extendByZeroₗᵢ (mu := mu) (p := p) hsub (v : Sobolev1JetLp mu Omega p) :=
    (Sobolev1JetLp.extendByZeroₗᵢ hsub).continuous.comp continuous_subtype_val
  refine w1p0Submodule_subset_of_isClosed (hclosed.preimage hcont) (fun phi => ?_) hu
  exact ⟨W1p.ofTestFunctionₗ mu Omega' p (TestFunction.monoCLM ℝ phi),
    W1p.ofTestFunctionₗ_mem_w1p0Submodule _,
    (Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ hsub phi).symm⟩

 

private theorem mem_w1p0Submodule_of_coe_eq (hsub : Omega ≤ Omega') {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) {v : W1p mu Omega' p}
    (hv : (v : Sobolev1JetLp mu Omega' p) =
      Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p)) :
    v ∈ w1p0Submodule mu Omega' p := by
  obtain ⟨w, hw, hwval⟩ := extendByZero_mem_image hsub hu
  exact Subtype.ext (hwval.trans hv.symm) ▸ hw

 


theorem Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule (hsub : Omega ≤ Omega')
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p) ∈
      w1pSubmodule mu Omega' p := by
  obtain ⟨v, -, hv⟩ := extendByZero_mem_image hsub hu
  exact hv ▸ v.2

 




def W1p0.extendByZeroL (hsub : Omega ≤ Omega') :
    W1p0 mu Omega p →L[ℝ] W1p0 mu Omega' p :=
  ContinuousLinearMap.codRestrict
    (ContinuousLinearMap.codRestrict
      ((Sobolev1JetLp.extendByZeroₗᵢ (mu := mu) (p := p) hsub).toContinuousLinearMap.comp
        ((w1pSubmodule mu Omega p).toSubmodule.subtypeL.comp
          (w1p0Submodule mu Omega p).toSubmodule.subtypeL))
      (w1pSubmodule mu Omega' p).toSubmodule
      fun u => Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule hsub u.2)
    (w1p0Submodule mu Omega' p).toSubmodule
    fun u => mem_w1p0Submodule_of_coe_eq hsub u.2 rfl

 
@[simp]
theorem W1p0.coe_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    ((W1p0.extendByZeroL hsub u : W1p mu Omega' p) : Sobolev1JetLp mu Omega' p) =
      Sobolev1JetLp.extendByZeroₗᵢ hsub ((u : W1p mu Omega p) : Sobolev1JetLp mu Omega p) :=
  (rfl)

 
@[simp]
theorem W1p0.extendByZeroL_self (u : W1p0 mu Omega p) : W1p0.extendByZeroL le_rfl u = u :=
  Subtype.ext (Subtype.ext (extendByZeroLpₗᵢ_self ℝ _ _))

 
@[simp]
theorem W1p0.extendByZeroL_extendByZeroL (hsub : Omega ≤ Omega') (hsub' : Omega' ≤ Omega'')
    (u : W1p0 mu Omega p) :
    W1p0.extendByZeroL hsub' (W1p0.extendByZeroL hsub u) =
      W1p0.extendByZeroL (hsub.trans hsub') u :=
  Subtype.ext (Subtype.ext (extendByZeroLpₗᵢ_extendByZeroLpₗᵢ ℝ _ _ _ _ _))

 


theorem W1p0.norm_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    ‖W1p0.extendByZeroL hsub u‖ = ‖u‖ :=
  (Sobolev1JetLp.extendByZeroₗᵢ hsub).norm_map _

 
@[simp]
theorem W1p0.value_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    W1p.value (W1p0.extendByZeroL hsub u : W1p mu Omega' p) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.value (u : W1p mu Omega p)) := by
  rw [W1p.value_coe, W1p.value_coe, W1p0.coe_extendByZeroL,
    Sobolev1JetLp.value_extendByZeroₗᵢ]

 


theorem W1p0.value_extendByZeroL_ae_eq_zero_compl (u : W1p0 mu Omega p) :
    ∀ᵐ x ∂mu, x ∉ (Omega : Set E) →
      W1p.value (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) x = 0 := by
  rw [W1p0.value_extendByZeroL (Omega' := ⊤) le_top u]
  have hvalue : ⇑(extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤))
      (W1p.value (u : W1p mu Omega p))) =ᵐ[mu]
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤)) (W1p.value (u : W1p mu Omega p))
  filter_upwards [hvalue] with x hx hxo
  rw [hx, Set.indicator_of_notMem hxo]

 
@[simp]
theorem W1p0.gradient_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    W1p.gradient (W1p0.extendByZeroL hsub u : W1p mu Omega' p) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.gradient (u : W1p mu Omega p)) := by
  rw [W1p.gradient_coe, W1p.gradient_coe, W1p0.coe_extendByZeroL,
    Sobolev1JetLp.gradient_extendByZeroₗᵢ]

 




theorem W1p0.hasWeakFDerivOn_indicator (hsub : Omega ≤ Omega')
    (u : W1p0 mu Omega p) :
    HasWeakFDerivOn mu Omega'
      ((Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ))
      fun x => innerSL ℝ
        ((Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p) : E → E) x) := by
  have hbridge :=
    (W1p.value_coe (W1p0.extendByZeroL hsub u : W1p mu Omega' p)).symm
  have hmem := (mem_w1pSubmodule_iff_hasWeakFDerivOn
    ((W1p0.extendByZeroL hsub u : W1p mu Omega' p) : Sobolev1JetLp mu Omega' p)).mp
      (W1p0.extendByZeroL hsub u : W1p mu Omega' p).2
  rw [hbridge] at hmem
  have hvalue : (W1p.value (W1p0.extendByZeroL hsub u : W1p mu Omega' p) : E → ℝ)
      =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
    rw [W1p0.value_extendByZeroL]
    exact coeFn_extendByZeroLpₗᵢ _ _ _ _
  have hgradient : (W1p.gradient (W1p0.extendByZeroL hsub u : W1p mu Omega' p) : E → E)
      =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p) : E → E) := by
    rw [W1p0.gradient_extendByZeroL]
    exact coeFn_extendByZeroLpₗᵢ _ _ _ _
  refine (hmem.congr_ae hvalue).congr_ae_deriv ?_
  filter_upwards [hgradient] with x hx
  refine ContinuousLinearMap.ext fun v => ?_
  rw [Sobolev1JetLp.candidateWeakFDeriv_apply, innerSL_apply_apply, ← W1p.gradient_coe, hx]
  exact real_inner_comm _ _

end TauCeti
