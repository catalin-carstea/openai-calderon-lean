/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import Proof.TauCeti.Analysis.PDE.EnergyForm.Sobolev

 

























































































public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {C : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

 

 



def dirichletForcing (f : Lp ℝ 2 (mu.restrict Omega)) : StrongDual ℝ (W1p0 mu Omega 2) :=
  (innerSL ℝ f).comp W1p0.valueL

 
@[simp] theorem dirichletForcing_apply (f : Lp ℝ 2 (mu.restrict Omega)) (v : W1p0 mu Omega 2) :
    dirichletForcing f v = ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [dirichletForcing, ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p0.valueL_apply]

 
theorem dirichletForcing_apply_eq_setIntegral (f : Lp ℝ 2 (mu.restrict Omega))
    (v : W1p0 mu Omega 2) :
    dirichletForcing f v = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  rw [dirichletForcing_apply, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [RCLike.inner_apply, mul_comm])

 

theorem norm_dirichletForcing_apply_le (f : Lp ℝ 2 (mu.restrict Omega))
    (v : W1p0 mu Omega 2) : ‖dirichletForcing f v‖ ≤ ‖f‖ * ‖v‖ := by
  rw [dirichletForcing_apply]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (W1p.norm_value_le (v : W1p mu Omega 2)) (norm_nonneg f)

 
theorem norm_dirichletForcing_le (f : Lp ℝ 2 (mu.restrict Omega)) :
    ‖dirichletForcing f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (norm_dirichletForcing_apply_le f)

 

 








def IsWeakSolutionDirichlet (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) : Prop :=
  ∀ v : W1p0 mu Omega 2,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = dirichletForcing f v

 
@[simp] theorem isWeakSolutionDirichlet_iff (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet a b c f u ↔
      ∀ v : W1p0 mu Omega 2,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2)
          = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [IsWeakSolutionDirichlet, dirichletForcing_apply_eq_setIntegral]

 



theorem isWeakSolutionDirichlet_iff_forall_testFunction
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet a b c f u ↔
      ∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 a b c (u : W1p mu Omega 2) (W1p.ofTestFunctionₗ mu Omega 2 φ)
          = ∫ x in Omega, f x * φ x ∂mu := by
   
  have hforce : ∀ φ : 𝓓(Omega, ℝ), ⟪f, W1p.value (W1p.ofTestFunctionₗ mu Omega 2 φ)⟫_ℝ
      = ∫ x in Omega, f x * φ x ∂mu := fun φ => by
    have h := dirichletForcing_apply_eq_setIntegral f
      ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule (p := 2) φ⟩
    rw [dirichletForcing_apply] at h
    refine h.trans (integral_congr_ae ?_)
    filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
    rw [W1p.value_ofTestFunctionₗ, hx]
  refine ⟨fun h φ => ?_, fun h v => ?_⟩
  · rw [← hforce]
    exact (h ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).trans (dirichletForcing_apply f _)
  · have hclosed : IsClosed {v : W1p mu Omega 2 |
        energyFormH1L hcoeff (u : W1p mu Omega 2) v = ⟪f, W1p.value v⟫_ℝ} :=
      isClosed_eq (energyFormH1L hcoeff _).continuous
        (((innerSL ℝ f).continuous.comp W1p.valueL.continuous).congr fun v => by
          simp only [Function.comp_apply, innerSL_apply_apply]
          exact congrArg _ (W1p.valueL_apply v))
    have hmem := w1p0Submodule_subset_of_isClosed hclosed
      (fun φ => by simpa only [Set.mem_ofPred_eq, energyFormH1L_apply, hforce] using h φ) v.2
    rw [dirichletForcing_apply, ← energyFormH1L_apply hcoeff]
    exact hmem

 


theorem norm_le_of_isWeakSolutionDirichlet (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) : ‖u‖ ≤ ‖f‖ / C := by
  have hkey : C * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ :=
    ((hlower u).trans_eq (hu u)).trans ((le_abs_self _).trans (norm_dirichletForcing_apply_le f u))
  rcases eq_or_lt_of_le (norm_nonneg u) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (norm_nonneg f) hC.le
  · rw [le_div_iff₀ hC]
    nlinarith [hkey, hpos]

 

 


theorem isCoercive_energyFormH1L0
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2)) :
    IsCoercive (energyFormH1L0 hcoeff) := by
  refine ⟨C, hC, fun w => ?_⟩
  rw [energyFormH1L0_apply]
  calc C * ‖w‖ * ‖w‖ = C * ‖w‖ ^ 2 := by ring
    _ ≤ _ := hlower w

 



def weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    W1p0 mu Omega 2 :=
  hcoercive.solutionOfFunctional (dirichletForcing f)

 
theorem isWeakSolutionDirichlet_weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    IsWeakSolutionDirichlet a b c f (weakSolutionDirichlet hcoeff hcoercive f) := by
  intro v
  rw [← energyFormH1L0_apply hcoeff]
  exact hcoercive.apply_solutionOfFunctional_eq (dirichletForcing f) v

 
theorem eq_weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p0 mu Omega 2} (hu : IsWeakSolutionDirichlet a b c f u) :
    u = weakSolutionDirichlet hcoeff hcoercive f :=
  hcoercive.eq_solutionOfFunctional fun v => by
    rw [energyFormH1L0_apply hcoeff]; exact hu v

 







theorem existsUnique_isWeakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u :=
  ⟨weakSolutionDirichlet hcoeff hcoercive f,
    isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive f,
    fun _ hu => eq_weakSolutionDirichlet hcoeff hcoercive hu⟩

 

theorem existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u :=
  existsUnique_isWeakSolutionDirichlet hcoeff (isCoercive_energyFormH1L0 hcoeff hC hlower) f

 



theorem UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_mass_lower_bound
    [DecidableEq ι] {lam Lam beta gamma delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), delta ≤ c x)
    (hmass : beta ^ 2 < 4 * lam * delta) (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u := by
  have hdelta : 0 < delta := by
    have : 0 < 4 * lam * delta := lt_of_le_of_lt (sq_nonneg beta) hmass
    exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) h.pos)).mp this
  have hquot : beta ^ 2 / (4 * delta) < lam := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hdelta)).mpr
    nlinarith [hmass]
  obtain ⟨eps, hlo, hhi⟩ := exists_between hquot
  have heps : 0 < eps := lt_of_le_of_lt (by positivity) hlo
  have hdefect : beta ^ 2 / (4 * eps) < delta := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) heps)).mpr
    have hmul := (div_lt_iff₀ (mul_pos (by norm_num) hdelta)).mp hlo
    nlinarith [hmul]
  exact existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (lt_min (sub_pos.mpr hhi) (sub_pos.mpr hdefect))
    (fun w => h.min_mul_norm_sq_le_energyFormH1_self_of_mass_lower_bound_with_parameter ha hb hc
      hb_bound hc_bound hc_lower heps w) f

 

 

@[simp] theorem energyFormH1_one_zero_zero_apply [DecidableEq ι] (u v : W1p mu Omega 2) :
    energyFormH1 (fun _ => 1) 0 0 u v =
      ∫ x in Omega, W1p.gradient v x ⬝ᵥ W1p.gradient u x ∂mu := by
  rw [energyFormH1_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp)

 

theorem isWeakSolutionDirichlet_one_zero_zero_iff [DecidableEq ι]
    (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u ↔
      ∀ v : W1p0 mu Omega 2,
        ∫ x in Omega, W1p.gradient (v : W1p mu Omega 2) x ⬝ᵥ
            W1p.gradient (u : W1p mu Omega 2) x ∂mu
          = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [isWeakSolutionDirichlet_iff, energyFormH1_one_zero_zero_apply]

end Domain

 

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

 





theorem existsUnique_isWeakSolutionDirichlet_of_subset_slab
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega)) (hbeta : 0 ≤ beta)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {i : Fin (n + 1)} {s t : ℝ} (hst : s ≤ t)
    (hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc s t)
    (hsmall : beta * (t - s) < lam)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet a b c f u :=
  existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (energyFormH1_poincare_constant_pos h.pos hbeta (by linarith) hsmall)
    (fun w => mul_norm_sq_le_energyFormH1_self_of_subset_slab h ha hb hc hb_bound hc_bound
      hc_nonneg hst hslab w.2) f

 




theorem existsUnique_isWeakSolutionDirichlet_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega)) (hbeta : 0 ≤ beta)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hsmall : beta * (2 * R) < lam)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet a b c f u :=
  existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (energyFormH1_poincare_constant_pos h.pos hbeta (by linarith) hsmall)
    (fun w => mul_norm_sq_le_energyFormH1_self_of_subset_ball h ha hb hc hb_bound hc_bound
      hc_nonneg hball w.2) f

end UniformlyEllipticOn

 

 







theorem existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u :=
  UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball
    (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const le_rfl (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp)
    (fun _ _ => le_rfl) hR hball (by simp) f

end Euclidean

end PDE

end TauCeti
