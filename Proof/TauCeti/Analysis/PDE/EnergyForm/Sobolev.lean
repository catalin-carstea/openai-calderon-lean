/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.TauCeti.Analysis.PDE.EnergyForm.Integrability
public import Proof.TauCeti.Analysis.PDE.EnergyForm.Integrated.Basic
public import Proof.TauCeti.Analysis.PDE.EnergyForm.Integrated.Symmetry
public import Proof.TauCeti.Analysis.PDE.EnergyForm.VariableLp
public import Proof.TauCeti.Analysis.Sobolev.Poincare.W1p0

 




























































































































public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace

 

section JetField

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

 






def jetField (u : W1p mu Omega p) : E → ℝ × E :=
  fun x => (W1p.value u x, W1p.gradient u x)

 
@[simp]
theorem jetField_apply (u : W1p mu Omega p) (x : E) :
    jetField u x = (W1p.value u x, W1p.gradient u x) :=
  by
    unfold jetField
    rfl

private theorem jetField_zero_ae :
    jetField (0 : W1p mu Omega p) =ᵐ[mu.restrict Omega] 0 := by
  have hval : W1p.value (0 : W1p mu Omega p) = 0 := by
    rw [← W1p.valueL_apply]
    exact map_zero (W1p.valueL (mu := mu) (Omega := Omega) (p := p))
  have hgrad : W1p.gradient (0 : W1p mu Omega p) = 0 := by
    rw [← W1p.gradientL_apply]
    exact map_zero (W1p.gradientL (mu := mu) (Omega := Omega) (p := p))
  filter_upwards [Lp.coeFn_zero (E := ℝ) (p := p) (μ := mu.restrict Omega),
    Lp.coeFn_zero (E := E) (p := p) (μ := mu.restrict Omega)] with x hx hy
  rw [jetField_apply, hval, hgrad]
  exact Prod.ext hx hy

private theorem jetField_add_ae (u v : W1p mu Omega p) :
    jetField (u + v) =ᵐ[mu.restrict Omega] fun x => jetField u x + jetField v x := by
  have hval : W1p.value (u + v) = W1p.value u + W1p.value v := by
    simp only [← W1p.valueL_apply, map_add]
  have hgrad : W1p.gradient (u + v) = W1p.gradient u + W1p.gradient v := by
    simp only [← W1p.gradientL_apply, map_add]
  filter_upwards [Lp.coeFn_add (W1p.value u) (W1p.value v),
    Lp.coeFn_add (W1p.gradient u) (W1p.gradient v)] with x hx hy
  simp only [jetField_apply, hval, hgrad]
  exact Prod.ext hx hy

private theorem jetField_smul_ae (r : ℝ) (u : W1p mu Omega p) :
    jetField (r • u) =ᵐ[mu.restrict Omega] fun x => r • jetField u x := by
  have hval : W1p.value (r • u) = r • W1p.value u := by
    simp only [← W1p.valueL_apply, map_smul]
  have hgrad : W1p.gradient (r • u) = r • W1p.gradient u := by
    simp only [← W1p.gradientL_apply, map_smul]
  filter_upwards [Lp.coeFn_smul r (W1p.value u), Lp.coeFn_smul r (W1p.gradient u)] with x hx hy
  simp only [jetField_apply, hval, hgrad]
  exact Prod.ext hx hy

 

theorem memLp_jetField (u : W1p mu Omega p) : MemLp (jetField u) p (mu.restrict Omega) :=
  MemLp.of_fst_snd ⟨Lp.memLp (W1p.value u), Lp.memLp (W1p.gradient u)⟩

end JetField

private theorem ae_mem_restrict {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
    [OpensMeasurableSpace alpha] {mu : Measure alpha} {Omega : Opens alpha} :
    ∀ᵐ x ∂mu.restrict (Omega : Set alpha), x ∈ (Omega : Set alpha) :=
  ae_restrict_mem Omega.isOpen.measurableSet

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
  {lam Lam beta gamma P : ℝ}

 

theorem memLp_energyIntegrand_of_bounds
    (hLam : 0 ≤ Lam) (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (ha_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ∀ eta xi : EuclideanSpace ℝ ι,
        |dotProduct eta (Matrix.mulVec (a x) xi)| ≤ Lam * ‖eta‖ * ‖xi‖)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) :
    MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega) := by
  refine memLp_top_of_bound (f := fun x => energyIntegrand (a x) (b x) (c x))
    (aestronglyMeasurable_energyIntegrand ha hb hc) (Lam + beta + gamma) ?_
  exact (ae_mem_restrict (mu := mu) (Omega := Omega)).mono fun x hx =>
    opNorm_energyIntegrand_le_of_bounds hLam (ha_bound x hx) (hb_bound x hx) (hc_bound x hx)

 

theorem memLp_energyIntegrand_mass_sub_const
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (kappa : ℝ) :
    MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x - kappa)) ⊤ (mu.restrict Omega) := by
  let : NormedAddCommGroup
      ((ℝ × EuclideanSpace ℝ ι) →L[ℝ] (ℝ × EuclideanSpace ℝ ι) →L[ℝ] ℝ) := inferInstance
  have hconst :
      MemLp (fun _ : EuclideanSpace ℝ ι ↦ energyIntegrand (0 : Matrix ι ι ℝ) 0 kappa)
        ⊤ (mu.restrict Omega) :=
    memLp_top_const
      (E := (ℝ × EuclideanSpace ℝ ι) →L[ℝ] (ℝ × EuclideanSpace ℝ ι) →L[ℝ] ℝ)
      (μ := mu.restrict Omega) (energyIntegrand (0 : Matrix ι ι ℝ) 0 kappa)
  have hsub := hcoeff.sub hconst
  apply MemLp.ae_eq (hf_Lp := hsub)
  filter_upwards with x
  simp only [Pi.sub_apply]
  simpa only [sub_zero] using
    (energyIntegrand_sub (a x) 0 (b x) 0 (c x) kappa).symm

variable [mu.IsAddHaarMeasure]

 

def jetLpL : W1p mu Omega 2 →L[ℝ]
    Lp (ℝ × EuclideanSpace ℝ ι) 2 (mu.restrict Omega) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (EuclideanSpace ℝ ι)).toContinuousLinearMap.compLpL
      2 (mu.restrict Omega)).comp
    (w1pSubmodule mu Omega 2).toSubmodule.subtypeL

 
theorem jetLpL_apply_ae (u : W1p mu Omega 2) :
    jetLpL u =ᵐ[mu.restrict Omega] jetField u := by
  filter_upwards [
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
      (EuclideanSpace ℝ ι)).toContinuousLinearMap.coeFn_compLpL (u : Sobolev1JetLp mu Omega 2),
    W1p.value_apply_ae u, W1p.gradient_apply_ae u] with x hjet hvalue hgradient
  rw [jetField_apply]
   
   
  have hcomp : jetLpL u =
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
        (EuclideanSpace ℝ ι)).toContinuousLinearMap.compLpL 2 (mu.restrict Omega))
        (u : Sobolev1JetLp mu Omega 2) := (rfl)
  rw [hcomp, hjet]
  simpa only [WithLp.prodContinuousLinearEquiv_apply] using
    Prod.ext hvalue.symm hgradient.symm

 
theorem integrable_norm_jetField_snd_sq (u : W1p mu Omega 2) :
    Integrable (fun x => ‖(jetField u x).2‖ ^ 2) (mu.restrict Omega) := by
  simpa only [jetField_apply] using W1p.integrable_norm_gradient_sq u

 
theorem integrable_jetField_fst_sq (u : W1p mu Omega 2) :
    Integrable (fun x => (jetField u x).1 ^ 2) (mu.restrict Omega) := by
  simpa only [jetField_apply] using W1p.integrable_value_sq u

 

theorem integral_norm_jetField_snd_sq_eq_norm_gradient_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, ‖(jetField u x).2‖ ^ 2 ∂mu = ‖W1p.gradient u‖ ^ 2 := by
  simpa only [jetField_apply] using W1p.integral_norm_gradient_sq_eq_norm_gradient_sq u

 

theorem integral_jetField_fst_sq_eq_norm_value_sq (u : W1p mu Omega 2) :
    ∫ x in Omega, (jetField u x).1 ^ 2 ∂mu = ‖W1p.value u‖ ^ 2 := by
  simpa only [jetField_apply] using W1p.integral_value_sq_eq_norm_value_sq u

 


theorem integral_norm_jetField_sq_le (u : W1p mu Omega 2) :
    ∫ x in Omega, ‖jetField u x‖ ^ 2 ∂mu ≤ ‖u‖ ^ 2 := by
  have hgrad := integrable_norm_jetField_snd_sq u
  have hval := integrable_jetField_fst_sq u
  have hjet : Integrable (fun x => ‖jetField u x‖ ^ 2) (mu.restrict Omega) :=
    (memLp_two_iff_integrable_sq_norm (memLp_jetField u).aestronglyMeasurable).1
      (memLp_jetField u)
  have hpoint : ∀ x, ‖jetField u x‖ ^ 2
      ≤ (jetField u x).1 ^ 2 + ‖(jetField u x).2‖ ^ 2 := fun x => by
    rw [Prod.norm_def, ← sq_abs (jetField u x).1, ← Real.norm_eq_abs]
    rcases le_total ‖(jetField u x).1‖ ‖(jetField u x).2‖ with hle | hle
    · rw [max_eq_right hle]
      nlinarith [sq_nonneg ‖(jetField u x).1‖]
    · rw [max_eq_left hle]
      nlinarith [sq_nonneg ‖(jetField u x).2‖]
  calc ∫ x in Omega, ‖jetField u x‖ ^ 2 ∂mu
      ≤ ∫ x in Omega, ((jetField u x).1 ^ 2 + ‖(jetField u x).2‖ ^ 2) ∂mu :=
        integral_mono hjet (hval.add hgrad) hpoint
    _ = ‖W1p.value u‖ ^ 2 + ‖W1p.gradient u‖ ^ 2 := by
        rw [integral_add hval hgrad, integral_jetField_fst_sq_eq_norm_value_sq,
          integral_norm_jetField_snd_sq_eq_norm_gradient_sq]
    _ = ‖u‖ ^ 2 := (W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u).symm

 



theorem integral_norm_jetField_mul_le (u v : W1p mu Omega 2) :
    ∫ x in Omega, ‖jetField u x‖ * ‖jetField v x‖ ∂mu ≤ ‖u‖ * ‖v‖ := by
  have hholder : ∫ x in Omega, ‖jetField u x‖ * ‖jetField v x‖ ∂mu
      ≤ √(∫ x in Omega, ‖jetField u x‖ ^ 2 ∂mu) *
        √(∫ x in Omega, ‖jetField v x‖ ^ 2 ∂mu) := by
    have hu : MemLp (jetField u) (ENNReal.ofReal (2 : ℝ)) (mu.restrict Omega) := by
      simpa using memLp_jetField u
    have hv : MemLp (jetField v) (ENNReal.ofReal (2 : ℝ)) (mu.restrict Omega) := by
      simpa using memLp_jetField v
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using
      (integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        hu hv)
  refine hholder.trans (mul_le_mul ?_ ?_ (Real.sqrt_nonneg _) (norm_nonneg u))
  · exact Real.sqrt_le_iff.mpr ⟨norm_nonneg u, integral_norm_jetField_sq_le u⟩
  · exact Real.sqrt_le_iff.mpr ⟨norm_nonneg v, integral_norm_jetField_sq_le v⟩

 

 







def energyFormH1 (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (u v : W1p mu Omega 2) : ℝ :=
  energyFormIntegral (mu.restrict Omega) a b c (jetField u) (jetField v)

 
theorem energyFormH1_def (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (u v : W1p mu Omega 2) :
    energyFormH1 a b c u v =
      ∫ x in Omega, energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x) ∂mu :=
  energyFormIntegral_def _ _ _ _ _ _

 



theorem energyFormH1_const_eq_setIntegral (A : Matrix ι ι ℝ) (u v : W1p mu Omega 2) :
    energyFormH1 (fun _ => A) 0 0 u v
      = ∫ x in Omega, matrixBilinearForm A (W1p.gradient v x) (W1p.gradient u x) ∂mu := by
  rw [energyFormH1_def]
  simp

 
@[simp]
theorem energyFormH1_zero_left (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (v : W1p mu Omega 2) : energyFormH1 a b c 0 v = 0 := by
  calc
    energyFormH1 a b c 0 v =
        energyFormIntegral (mu.restrict Omega) a b c 0 (jetField v) :=
      energyFormIntegral_congr_ae (mu.restrict Omega) a b c (jetField 0) (jetField v)
        .rfl .rfl .rfl jetField_zero_ae .rfl
    _ = 0 := energyFormIntegral_zero_left _ _ _ _ _

 
@[simp]
theorem energyFormH1_zero_right (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (u : W1p mu Omega 2) : energyFormH1 a b c u 0 = 0 := by
  calc
    energyFormH1 a b c u 0 =
        energyFormIntegral (mu.restrict Omega) a b c (jetField u) 0 :=
      energyFormIntegral_congr_ae (mu.restrict Omega) a b c (jetField u) (jetField 0)
        .rfl .rfl .rfl .rfl jetField_zero_ae
    _ = 0 := energyFormIntegral_zero_right _ _ _ _ _

 
@[simp]
theorem energyFormH1_smul_left (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (r : ℝ) (u v : W1p mu Omega 2) :
    energyFormH1 a b c (r • u) v = r * energyFormH1 a b c u v := by
  calc
    energyFormH1 a b c (r • u) v =
        energyFormIntegral (mu.restrict Omega) a b c (fun x => r • jetField u x) (jetField v) :=
      energyFormIntegral_congr_ae (mu.restrict Omega) a b c (jetField (r • u)) (jetField v)
        .rfl .rfl .rfl (jetField_smul_ae r u) .rfl
    _ = r * energyFormH1 a b c u v := energyFormIntegral_smul_left _ _ _ _ _ _ r

 
@[simp]
theorem energyFormH1_smul_right (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (r : ℝ) (u v : W1p mu Omega 2) :
    energyFormH1 a b c u (r • v) = r * energyFormH1 a b c u v := by
  calc
    energyFormH1 a b c u (r • v) =
        energyFormIntegral (mu.restrict Omega) a b c (jetField u) (fun x => r • jetField v x) :=
      energyFormIntegral_congr_ae (mu.restrict Omega) a b c (jetField u) (jetField (r • v))
        .rfl .rfl .rfl .rfl (jetField_smul_ae r v)
    _ = r * energyFormH1 a b c u v := energyFormIntegral_smul_right _ _ _ _ _ _ r

 



theorem energyFormH1_comm_of_isSymm_ae
    (ha : ∀ᵐ x ∂mu.restrict (Omega : Set (EuclideanSpace ℝ ι)), (a x).IsSymm)
    (u v : W1p mu Omega 2) :
    energyFormH1 a 0 c u v = energyFormH1 a 0 c v u :=
  energyFormIntegral_zero_drift_comm_of_isSymm_ae ha

 



theorem energyFormH1_poincare_constant_pos (hlam : 0 < lam) (hbeta : 0 ≤ beta) (hP : 0 ≤ P)
    (hsmall : beta * P < lam) :
    0 < (lam ^ 2 - beta ^ 2 * P ^ 2) / (2 * lam * (P ^ 2 + 1)) := by
  have hD : 0 < 2 * lam * (P ^ 2 + 1) := by positivity
  refine div_pos ?_ hD
  nlinarith [mul_nonneg hbeta hP]

 

private theorem mul_norm_sq_le_of_gradient_sub_value_bound {A B q : ℝ}
    {u : W1p mu Omega 2} (hAB : 0 ≤ A + B)
    (hlower : A * ‖W1p.gradient u‖ ^ 2 - B * ‖W1p.value u‖ ^ 2 ≤ q)
    (hu : ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    (A - B * P ^ 2) / (P ^ 2 + 1) * ‖u‖ ^ 2 ≤ q := by
  have hP : 0 < P ^ 2 + 1 := by positivity
  have hnorm := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  have hsq : ‖W1p.value u‖ ^ 2 ≤ P ^ 2 * ‖W1p.gradient u‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg (W1p.value u)) hu
    nlinarith [this]
  refine le_trans ?_ hlower
  rw [div_mul_eq_mul_div, div_le_iff₀ hP, hnorm]
  nlinarith [mul_nonneg hAB (sub_nonneg.2 hsq)]

 

noncomputable local instance instSeminormedAddCommGroupW1p :
    SeminormedAddCommGroup (W1p mu Omega 2) := inferInstance

 

noncomputable local instance instNormedSpaceW1p :
    NormedSpace ℝ (W1p mu Omega 2) := inferInstance

 

theorem integrable_energyIntegrand_jetField
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1p mu Omega 2) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x))
      (mu.restrict Omega) := by
  refine (integrable_bilinear_apply_of_memLp hcoeff (jetLpL u) (jetLpL v)).congr ?_
  filter_upwards [jetLpL_apply_ae u, jetLpL_apply_ae v] with x hu hv
  rw [hu, hv]

open scoped InnerProductSpace in
 

theorem energyFormH1_mass_sub_const
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (kappa : ℝ) (u v : W1p mu Omega 2) :
    energyFormH1 a b (fun x ↦ c x - kappa) u v =
      energyFormH1 a b c u v - kappa * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  have hmass : Integrable (fun x ↦ W1p.value u x * W1p.value v x) (mu.restrict Omega) := by
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      L2.integrable_inner (𝕜 := ℝ) (W1p.value u) (W1p.value v)
  rw [energyFormH1_def, energyFormH1_def, W1p.inner_value_eq_setIntegral,
    ← integral_const_mul, ← integral_sub (integrable_energyIntegrand_jetField hcoeff u v)
      (hmass.const_mul kappa)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [energyIntegrand_apply, massForm_apply, jetField_apply]
  ring

 

def energyFormH1L
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    W1p mu Omega 2 →L[ℝ] W1p mu Omega 2 →L[ℝ] ℝ :=
  (energyFormLpVariable (mu.restrict Omega) a b c hcoeff).bilinearComp jetLpL jetLpL

 
@[simp]
theorem energyFormH1L_apply
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1p mu Omega 2) :
    energyFormH1L hcoeff u v = energyFormH1 a b c u v := by
  rw [energyFormH1L, ContinuousLinearMap.bilinearComp_apply, energyFormLpVariable_apply,
    energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [jetLpL_apply_ae u, jetLpL_apply_ae v] with x hu hv
  rw [hu, hv]

 
theorem energyFormH1_add_left
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v w : W1p mu Omega 2) :
    energyFormH1 a b c (u + w) v = energyFormH1 a b c u v + energyFormH1 a b c w v := by
  rw [← energyFormH1L_apply hcoeff]
  simp only [map_add, add_apply, energyFormH1L_apply]

 
theorem energyFormH1_add_right
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v w : W1p mu Omega 2) :
    energyFormH1 a b c u (v + w) = energyFormH1 a b c u v + energyFormH1 a b c u w := by
  rw [← energyFormH1L_apply hcoeff, map_add]
  simp only [energyFormH1L_apply]

 

theorem norm_energyFormH1_le_of_bounds
    (hLam : 0 ≤ Lam)
    (ha_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ∀ eta xi : EuclideanSpace ℝ ι,
        |dotProduct eta (Matrix.mulVec (a x) xi)| ≤ Lam * ‖eta‖ * ‖xi‖)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (u v : W1p mu Omega 2) :
    ‖energyFormH1 a b c u v‖ ≤ (Lam + beta + gamma) * (‖u‖ * ‖v‖) := by
  have hmem := ae_mem_restrict (mu := mu) (Omega := Omega)
  have hconst : 0 ≤ Lam + beta + gamma := by linarith
  have hmul : Integrable (fun x => ‖jetField u x‖ * ‖jetField v x‖) (mu.restrict Omega) :=
    (memLp_jetField u).norm.integrable_mul (memLp_jetField v).norm
  have key := norm_energyFormIntegral_le_of_bounds (μ := mu.restrict Omega)
    (a := a) (b := b) (c := c) (U := jetField u) (V := jetField v)
    hLam (hmem.mono fun x hx => ha_bound x hx) (hmem.mono hb_bound) (hmem.mono hc_bound)
      (hmul.const_mul (Lam + beta + gamma))
  refine key.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_norm_jetField_mul_le u v) hconst

 

theorem norm_energyFormH1L_le_of_bounds
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hLam : 0 ≤ Lam)
    (ha_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)),
      ∀ eta xi : EuclideanSpace ℝ ι,
        |dotProduct eta (Matrix.mulVec (a x) xi)| ≤ Lam * ‖eta‖ * ‖xi‖)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma) :
    ‖energyFormH1L hcoeff‖ ≤ Lam + beta + gamma := by
  refine (energyFormH1L hcoeff).opNorm_le_bound₂ (by linarith) ?_
  intro u v
  rw [energyFormH1L_apply, mul_assoc]
  exact norm_energyFormH1_le_of_bounds hLam ha_bound hbeta hgamma hb_bound hc_bound u v

 

def energyFormH1L0
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2 →L[ℝ] ℝ :=
  (energyFormH1L hcoeff).bilinearComp
    (w1p0Submodule mu Omega 2).toSubmodule.subtypeL
    (w1p0Submodule mu Omega 2).toSubmodule.subtypeL

 

@[simp]
theorem energyFormH1L0_apply
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (u v : W1p0 mu Omega 2) :
    energyFormH1L0 hcoeff u v =
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) := by
  unfold energyFormH1L0
  rw [ContinuousLinearMap.bilinearComp_apply, energyFormH1L_apply]
  simp only [Submodule.subtypeL_apply]

 


theorem energyFormH1L0_comm
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ u v : W1p0 mu Omega 2,
      energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (v : W1p mu Omega 2) (u : W1p mu Omega 2))
    (u v : W1p0 mu Omega 2) :
    energyFormH1L0 hcoeff u v = energyFormH1L0 hcoeff v u := by
  rw [energyFormH1L0_apply, energyFormH1L0_apply]
  exact hsymm u v

open scoped InnerProductSpace in
 


theorem exists_forcing_energyFormH1_principal_eq {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ g : Lp ℝ 2 (mu.restrict Omega), ∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have hB : MemLp (fun x => ⟪b x, W1p.gradient u x⟫_ℝ) 2 (mu.restrict Omega) :=
    MemLp.of_bilin (inner ℝ) 1 hb (Lp.memLp _) continuous_inner
      (.of_forall fun x => by simpa using nnnorm_inner_le_nnnorm (b x) (W1p.gradient u x))
  have hC : MemLp (fun x => c x * W1p.value u x) 2 (mu.restrict Omega) :=
    hc.fun_mul (Lp.memLp _)
  let G := fun x => f x - ⟪b x, W1p.gradient u x⟫_ℝ - c x * W1p.value u x
  have hG : MemLp G 2 (mu.restrict Omega) := ((Lp.memLp f).sub hB).sub hC
  refine ⟨hG.toLp G, fun v => ?_⟩
  have hv := Lp.memLp (W1p.value (v : W1p mu Omega 2))
  have hF : Integrable (fun x => f x * W1p.value (v : W1p mu Omega 2) x)
      (mu.restrict Omega) := (Lp.memLp f).integrable_mul hv
  have hBv : Integrable (fun x => ⟪b x, W1p.gradient u x⟫_ℝ *
      W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega) := hB.integrable_mul hv
  have hCv : Integrable (fun x => (c x * W1p.value u x) *
      W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega) := hC.integrable_mul hv
   
  have hdrift : Integrable (fun x => energyIntegrand 0 (b x) 0 (jetField u x)
      (jetField (v : W1p mu Omega 2) x)) (mu.restrict Omega) := by
    simpa [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply] using hBv
  have hmass : Integrable (fun x => energyIntegrand 0 0 (c x) (jetField u x)
      (jetField (v : W1p mu Omega 2) x)) (mu.restrict Omega) := by
    simpa [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply] using hCv
  have hdrift_eq : energyFormIntegral (mu.restrict Omega) (fun _ => 0) b (fun _ => 0)
      (jetField u) (jetField (v : W1p mu Omega 2)) =
        ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ * W1p.value (v : W1p mu Omega 2) x ∂mu := by
    rw [energyFormIntegral_def]
    simp [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply]
  have hmass_eq : energyFormIntegral (mu.restrict Omega) (fun _ => 0) (fun _ => 0) c
      (jetField u) (jetField (v : W1p mu Omega 2)) =
        ∫ x in Omega, (c x * W1p.value u x) * W1p.value (v : W1p mu Omega 2) x ∂mu := by
    rw [energyFormIntegral_def]
    simp [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply]
   
   
   
  have h := hu v
  rw [energyFormH1, energyFormIntegral_principal_drift_mass _ _ _ _ _ _
    (integrable_energyIntegrand_jetField ha u _) hdrift hmass, hdrift_eq, hmass_eq] at h
  rw [energyFormH1, Pi.zero_def, Pi.zero_def]
  calc
    _ = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu -
        ∫ x in Omega, ⟪b x, W1p.gradient u x⟫_ℝ *
          W1p.value (v : W1p mu Omega 2) x ∂mu -
        ∫ x in Omega, (c x * W1p.value u x) *
          W1p.value (v : W1p mu Omega 2) x ∂mu := by linarith
    _ = ∫ x in Omega, G x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
      simp only [G, sub_mul]
      rw [integral_sub (hF.sub' hBv) hCv, integral_sub hF hBv]
    _ = ∫ x in Omega, (hG.toLp G) x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
      apply integral_congr_ae
      filter_upwards [hG.coeFn_toLp] with x hx
      rw [hx]

namespace UniformlyEllipticOn

variable [DecidableEq ι]

 


private theorem withClassicalDecEq
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam) :
    @UniformlyEllipticOn (EuclideanSpace ℝ ι) ι _ (Classical.decEq ι)
      (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam := by
  rwa [Subsingleton.elim (Classical.decEq ι) ‹DecidableEq ι›]

 


theorem integrable_energyIntegrand_jetField
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (u v : W1p mu Omega 2) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField v x))
      (mu.restrict Omega) :=
  PDE.integrable_energyIntegrand_jetField
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound) u v

 









theorem norm_energyFormH1_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (u v : W1p mu Omega 2) :
    ‖energyFormH1 a b c u v‖ ≤ (Lam + beta + gamma) * (‖u‖ * ‖v‖) :=
  norm_energyFormH1_le_of_bounds h.upper_nonneg (fun _x hx eta xi => h.upper_bound hx eta xi)
    hbeta hgamma
    hb_bound hc_bound u v

 


theorem garding_energyFormH1_self_of_mass_lower_bound_with_parameter {delta eps : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), delta ≤ c x)
    (heps : 0 < eps) (u : W1p mu Omega 2) :
    (lam - eps) * ‖W1p.gradient u‖ ^ 2 +
        (delta - beta ^ 2 / (4 * eps)) * ‖W1p.value u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have hmem : ∀ᵐ x ∂mu.restrict (Omega : Set (EuclideanSpace ℝ ι)),
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) := ae_restrict_mem Omega.isOpen.measurableSet
  have hgrad := integrable_norm_jetField_snd_sq u
  have hval := integrable_jetField_fst_sq u
  have hlower := (hgrad.const_mul (lam - eps)).add
    (hval.const_mul (delta - beta ^ 2 / (4 * eps)))
  have key :=
    h.withClassicalDecEq.garding_energyFormIntegral_self_of_mass_lower_bound_with_parameter_on
      (μ := mu.restrict Omega) (b := b) (c := c) (U := jetField u) hmem
      (hmem.mono hb_bound) (hmem.mono hc_lower) heps hlower
      (integrable_energyIntegrand_jetField h ha hb hc hb_bound hc_bound u u)
  refine le_trans (le_of_eq ?_) key
  rw [integral_add (hgrad.const_mul _) (hval.const_mul _), integral_const_mul, integral_const_mul,
    integral_norm_jetField_snd_sq_eq_norm_gradient_sq,
    integral_jetField_fst_sq_eq_norm_value_sq]

 


theorem garding_energyFormH1_self_of_mass_lower_bound {delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), delta ≤ c x)
    (u : W1p mu Omega 2) :
    lam / 2 * ‖W1p.gradient u‖ ^ 2 +
        (delta - beta ^ 2 / (2 * lam)) * ‖W1p.value u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  convert h.garding_energyFormH1_self_of_mass_lower_bound_with_parameter ha hb hc
    hb_bound hc_bound hc_lower (half_pos h.pos) u using 1
  ring

 








theorem garding_energyFormH1_self
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) (u : W1p mu Omega 2) :
    lam / 2 * ‖W1p.gradient u‖ ^ 2 - beta ^ 2 / (2 * lam) * ‖W1p.value u‖ ^ 2
      ≤ energyFormH1 a b c u u := by
  simpa only [sub_eq_add_neg, zero_add, neg_mul] using
    garding_energyFormH1_self_of_mass_lower_bound h ha hb hc hb_bound hc_bound hc_nonneg u

 




theorem garding_energyFormH1_self_norm
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) (u : W1p mu Omega 2) :
    lam / 2 * ‖u‖ ^ 2 - (lam / 2 + beta ^ 2 / (2 * lam)) * ‖W1p.value u‖ ^ 2
      ≤ energyFormH1 a b c u u := by
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  convert garding_energyFormH1_self h ha hb hc hb_bound hc_bound hc_nonneg u using 1
  ring

 

theorem min_mul_norm_sq_le_energyFormH1_self_of_mass_lower_bound_with_parameter {delta eps : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), delta ≤ c x)
    (heps : 0 < eps) (u : W1p mu Omega 2) :
    min (lam - eps) (delta - beta ^ 2 / (4 * eps)) * ‖u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  refine le_trans ?_ (garding_energyFormH1_self_of_mass_lower_bound_with_parameter h ha hb hc
    hb_bound hc_bound hc_lower heps u)
  rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq, mul_add, add_comm]
  exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))

 


theorem min_mul_norm_sq_le_energyFormH1_self_of_mass_lower_bound {delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), delta ≤ c x)
    (u : W1p mu Omega 2) :
    min (lam / 2) (delta - beta ^ 2 / (2 * lam)) * ‖u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have hgrad : lam - lam / 2 = lam / 2 := by ring
  have hden : 4 * (lam / 2) = 2 * lam := by ring
  simpa only [hgrad, hden] using
    h.min_mul_norm_sq_le_energyFormH1_self_of_mass_lower_bound_with_parameter ha hb hc
      hb_bound hc_bound hc_lower (half_pos h.pos) u

 











theorem mul_norm_sq_le_energyFormH1_self_of_poincare
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    (lam ^ 2 - beta ^ 2 * P ^ 2) / (2 * lam * (P ^ 2 + 1)) * ‖u‖ ^ 2
      ≤ energyFormH1 a b c u u := by
  have hlam : 0 < lam := h.pos
  have hAB : 0 ≤ lam / 2 + beta ^ 2 / (2 * lam) := by positivity
  have key := mul_norm_sq_le_of_gradient_sub_value_bound (P := P) hAB
    (garding_energyFormH1_self h ha hb hc hb_bound hc_bound hc_nonneg u) hu
  convert key using 1
  field_simp

 






theorem mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_zero : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), b x = 0)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) (u : W1p mu Omega 2) :
    lam * ‖W1p.gradient u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have hmem := ae_mem_restrict (mu := mu) (Omega := Omega)
  have hb_zero_ae : b =ᵐ[mu.restrict Omega] fun _ => 0 := hmem.mono hb_zero
  have henergy_zero := integrable_energyIntegrand_jetField (b := fun _ => 0) (beta := 0)
    h ha aestronglyMeasurable_const hc (by simp) hc_bound u u
  have key := integral_mul_norm_snd_sq_le_energyFormIntegral_zero_drift_self
    (μ := mu.restrict Omega) (a := a) (c := c) (U := jetField u)
    (hmem.mono fun x hx xi => by
      simpa [Matrix.toQuadraticForm'_apply] using h.lower_bound hx xi)
    (hmem.mono hc_nonneg) ((integrable_norm_jetField_snd_sq u).const_mul lam) henergy_zero
  rw [← integral_norm_jetField_snd_sq_eq_norm_gradient_sq u, ← integral_const_mul,
    energyFormH1_def]
  exact key.trans_eq ((energyFormIntegral_congr_ae (μ := mu.restrict Omega)
    (a := a) (b := fun _ => 0) (c := c) (U := jetField u) (V := jetField u)
    Filter.EventuallyEq.rfl hb_zero_ae.symm Filter.EventuallyEq.rfl
      Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl).trans
        (energyFormIntegral_def _ _ _ _ _ _))

 







theorem div_mul_norm_sq_le_energyFormH1_self_of_zero_drift
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_zero : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), b x = 0)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) {u : W1p mu Omega 2}
    (hu : ‖W1p.value u‖ ≤ P * ‖W1p.gradient u‖) :
    lam / (P ^ 2 + 1) * ‖u‖ ^ 2 ≤ energyFormH1 a b c u u := by
  have key := mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift h ha hc hb_zero
    hc_bound hc_nonneg u
  simpa using mul_norm_sq_le_of_gradient_sub_value_bound (P := P) (by simpa using h.pos.le)
    (A := lam) (B := 0) (by simpa using key) hu

end UniformlyEllipticOn

end Domain

 

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

 








theorem mul_norm_sq_le_energyFormH1_self_of_subset_slab
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {i : Fin (n + 1)} {s t : ℝ} (hst : s ≤ t)
    (hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc s t)
    {u : W1p volume Omega 2} (hu : u ∈ w1p0Submodule volume Omega 2) :
    (lam ^ 2 - beta ^ 2 * (t - s) ^ 2) / (2 * lam * ((t - s) ^ 2 + 1)) * ‖u‖ ^ 2
      ≤ energyFormH1 a b c u u :=
  mul_norm_sq_le_energyFormH1_self_of_poincare h ha hb hc hb_bound hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_slab (ENNReal.ofNat_ne_top) hst hslab hu)

 







theorem mul_norm_sq_le_energyFormH1_self_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    {u : W1p volume Omega 2} (hu : u ∈ w1p0Submodule volume Omega 2) :
    (lam ^ 2 - beta ^ 2 * (2 * R) ^ 2) / (2 * lam * ((2 * R) ^ 2 + 1)) * ‖u‖ ^ 2
      ≤ energyFormH1 a b c u u :=
  mul_norm_sq_le_energyFormH1_self_of_poincare h ha hb hc hb_bound hc_bound hc_nonneg
    (W1p.norm_value_le_mul_norm_gradient_of_subset_ball (ENNReal.ofNat_ne_top) hball hu)

end UniformlyEllipticOn

end Euclidean

end PDE

end TauCeti
