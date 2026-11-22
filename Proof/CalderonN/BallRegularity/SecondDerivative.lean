module

public import Proof.CalderonN.BallRegularity.SobolevCalculus
public import Proof.CalderonN.BallRegularity.TangentialToH2
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.TestFunctionLp
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Ellipticity.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! From Proof/Archive/CollaboratorRegularitySecondDerivOct17.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace CalderonN.BallRegularity.SD

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE

variable (V : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 2)


def dv (k : Fin dim) : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2 := Wkp.firstOrder 0 (WkpCalculus.d k 1 V)

theorem value_dv (k : Fin dim) :
    ⇑(W1p.value (dv V k)) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => W1p.gradient (Wkp.lowerOrder 1 V) x k := by
  have h := WkpCalculus.value_d k 1 V
  rw [dv, Wkp.value_firstOrder]
  exact h


def sd (i k : Fin dim) : (X dim) → ℝ := fun x => W1p.gradient (dv V k) x i

lemma memLp_coord (G : Lp (X dim) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))) (k : Fin dim) :
    MemLp (fun x => G x k) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
  (EuclideanSpace.proj k : (X dim) →L[ℝ] ℝ).comp_memLp' (Lp.memLp G)

lemma li_coord (G : Lp (X dim) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))) (k : Fin dim) :
    LocallyIntegrableOn (fun x => G x k) ((fixedBallOpens dim) : Set (X dim)) volume :=
  TangH2.locallyIntegrableOn_of_memLp (memLp_coord G k)

lemma li_W (k : Fin dim) :
    LocallyIntegrableOn (fun x => W1p.gradient (Wkp.lowerOrder 1 V) x k) ((fixedBallOpens dim) : Set (X dim)) volume :=
  li_coord _ k

lemma li_sd (i k : Fin dim) : LocallyIntegrableOn (sd V i k) ((fixedBallOpens dim) : Set (X dim)) volume :=
  li_coord _ i


lemma hasWeakLineDerivOn_W (i k : Fin dim) :
    HasWeakLineDerivOn volume (fixedBallOpens dim) (fun x => W1p.gradient (Wkp.lowerOrder 1 V) x k)
      (sd V i k) (TangH2.e i) := by
  refine (((W1p.hasWeakFDerivOn (dv V k)) (TangH2.e i)).congr_ae (value_dv V k)).congr_ae_deriv ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [innerSL_apply_apply, sd]
  rw [TangH2.coord_eq_inner]

lemma integral_W_eq (i k : Fin dim) (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    ∫ x, lineDeriv ℝ (φ : (X dim) → ℝ) x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k =
      -∫ x, φ x * sd V i k x := by
  simpa only [smul_eq_mul] using
    (hasWeakLineDerivOn_W V i k).integral_lineDeriv_smul_eq_neg_integral_smul φ


lemma ae_zero_of_integral {g : (X dim) → ℝ} (hg : LocallyIntegrableOn g ((fixedBallOpens dim) : Set (X dim)) volume)
    (h : ∀ φ : 𝓓((fixedBallOpens dim), ℝ), ∫ x, φ x * g x = 0) :
    g =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] 0 := by
  have H : HasWeakLineDerivOn volume (fixedBallOpens dim) (0 : (X dim) → ℝ) g (TangH2.e 0) := by
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, locallyIntegrableOn_zero, hg, fun φ => ?_⟩
    simp only [Pi.zero_apply, smul_eq_mul, mul_zero, integral_zero, h φ, neg_zero]
  exact H.ae_eq hasWeakLineDerivOn_zero

theorem sd_symm (i k : Fin dim) :
    sd V i k =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] sd V k i := by
  have H : HasWeakLineDerivOn volume (fixedBallOpens dim) (fun x => W1p.gradient (Wkp.lowerOrder 1 V) x k)
      (sd V k i) (TangH2.e i) := by
    rw [hasWeakLineDerivOn_iff_testFunction]
    refine ⟨inferInstance, li_W V k, li_sd V k i, fun φ => ?_⟩
    have hs := TangH2.Tf_symm (W1p.hasWeakFDerivOn (Wkp.lowerOrder 1 V)) (li_W V) i k
    have h1 := congrArg (fun T => T φ) hs
    simp only [TangH2.Tf_apply (li_W V _)] at h1
    simp only [smul_eq_mul]
    rw [h1, integral_W_eq]
  exact (hasWeakLineDerivOn_W V i k).ae_eq H


lemma integrable_test_mul {g : (X dim) → ℝ} (hg : LocallyIntegrableOn g ((fixedBallOpens dim) : Set (X dim)) volume)
    (φ : 𝓓((fixedBallOpens dim), ℝ)) : Integrable (fun x => φ x * g x) volume := by
  simpa [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hg φ

lemma ibp_ik {c : (X dim) → ℝ} (hc : ContDiff ℝ ∞ c) (φ : 𝓓((fixedBallOpens dim), ℝ)) (i k : Fin dim) :
    ∫ x, lineDeriv ℝ (φ : (X dim) → ℝ) x (TangH2.e i) * (c x * W1p.gradient (Wkp.lowerOrder 1 V) x k) =
      -∫ x, (fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k +
        c x * sd V i k x) * φ x := by
  have hdc := TangH2.contDiff_fderiv_apply hc (TangH2.e i)
  have h := congrArg (fun T => T φ) (TangH2.mulF_Tf hc (li_W V k) i)
  simp only [TangH2.mulF, LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply] at h
  rw [TangH2.Tf_apply (li_W V k), TangH2.Tf_apply (TangH2.locallyIntegrableOn_mul hc.continuous (li_W V k)),
    TangH2.Pf_apply (li_W V k), integral_W_eq] at h
  have h1 : ∫ x, (TangH2.mulM c φ) x * sd V i k x = ∫ x, φ x * (c x * sd V i k x) := by
    congr 1; funext x; rw [TangH2.mulM_apply hc]; ring
  have h2 : ∫ x, (TangH2.mulM (fun x => fderiv ℝ c x (TangH2.e i)) φ) x *
      W1p.gradient (Wkp.lowerOrder 1 V) x k =
      ∫ x, φ x * (fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k) := by
    congr 1; funext x; rw [TangH2.mulM_apply hdc]; ring
  rw [h1, h2] at h
  have i1 := integrable_test_mul (TangH2.locallyIntegrableOn_mul hc.continuous (li_sd V i k)) φ
  have i2 := integrable_test_mul (TangH2.locallyIntegrableOn_mul hdc.continuous (li_W V k)) φ
  have h3 : ∫ x, (fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k +
        c x * sd V i k x) * φ x =
      (∫ x, φ x * (fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k)) +
        ∫ x, φ x * (c x * sd V i k x) := by
    rw [← integral_add i2 i1]; congr 1; funext x; ring
  rw [h3]; linarith


lemma setIntegral_test_eq {g : (X dim) → ℝ} (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    ∫ x in ((fixedBallOpens dim) : Set (X dim)), g x * φ x = ∫ x, g x * φ x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  rw [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem), mul_zero]


theorem integral_mbf_eq {M : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (hM : ContDiff ℝ ∞ M)
    (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (M x) (gradient (φ : (X dim) → ℝ) x)
        (W1p.gradient (Wkp.lowerOrder 1 V) x) =
      -∫ x in ((fixedBallOpens dim) : Set (X dim)),
        (∑ i, ∑ k, (fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single i 1) *
            W1p.gradient (Wkp.lowerOrder 1 V) x k + M x i k * sd V i k x)) * φ x := by
  have hA := TangH2.contDiff_entry hM
  have hawl : ∀ i k, LocallyIntegrableOn
      (fun x => M x i k * W1p.gradient (Wkp.lowerOrder 1 V) x k) ((fixedBallOpens dim) : Set (X dim)) volume :=
    fun i k => TangH2.locallyIntegrableOn_mul (hA i k).continuous (li_W V k)
  have hint : ∀ i k, Integrable (fun x => lineDeriv ℝ (φ : (X dim) → ℝ) x (TangH2.e i) *
      (M x i k * W1p.gradient (Wkp.lowerOrder 1 V) x k)) volume := fun i k => by
    simpa [smul_eq_mul] using integrable_lineDeriv_smul_of_locallyIntegrableOn (hawl i k) φ (TangH2.e i)
  have hint2 : ∀ i k, Integrable (fun x => (fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single i 1) *
      W1p.gradient (Wkp.lowerOrder 1 V) x k + M x i k * sd V i k x) * φ x) volume := fun i k => by
    have hli : LocallyIntegrableOn (fun x => fderiv ℝ (fun y => M y i k) x (EuclideanSpace.single i 1) *
        W1p.gradient (Wkp.lowerOrder 1 V) x k + M x i k * sd V i k x)
        ((fixedBallOpens dim) : Set (X dim)) volume :=
      (TangH2.locallyIntegrableOn_mul (TangH2.contDiff_fderiv_apply (hA i k) (EuclideanSpace.single i 1)).continuous
        (li_W V k)).add (TangH2.locallyIntegrableOn_mul (hA i k).continuous (li_sd V i k))
    simpa [mul_comm] using integrable_test_mul hli φ
  have hL : ∑ i, ∑ k, ∫ x, lineDeriv ℝ (φ : (X dim) → ℝ) x (TangH2.e i) *
        (M x i k * W1p.gradient (Wkp.lowerOrder 1 V) x k) =
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (M x) (gradient (φ : (X dim) → ℝ) x)
        (W1p.gradient (Wkp.lowerOrder 1 V) x) := by
    rw [Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun k _ => hint i k).symm]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := ((fixedBallOpens dim) : Set (X dim)))]
    · refine setIntegral_congr_fun (fixedBallOpens dim).isOpen.measurableSet fun x _ => ?_
      have hφx : DifferentiableAt ℝ (φ : (X dim) → ℝ) x := (φ.contDiff.differentiable (by simp)) x
      simp only [TangH2.matrixBilinearForm_eq_sum, TangH2.gradient_coord hφx]
    · intro x hx
      have hnot : x ∉ tsupport (φ : (X dim) → ℝ) := fun hmem => hx (φ.tsupport_subset hmem)
      simp [lineDeriv_eq_zero_of_notMem_tsupport φ hnot]
  rw [← hL, setIntegral_test_eq]
  simp only [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint2 i k]
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ => hint2 i k, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact ibp_ik V (hA i k) φ i k


lemma li_sum {ι : Type*} (s : Finset ι) {f : ι → (X dim) → ℝ}
    (h : ∀ i ∈ s, LocallyIntegrableOn (f i) ((fixedBallOpens dim) : Set (X dim)) volume) :
    LocallyIntegrableOn (fun x => ∑ i ∈ s, f i x) ((fixedBallOpens dim) : Set (X dim)) volume := by
  have := Finset.sum_induction f (fun g => LocallyIntegrableOn g ((fixedBallOpens dim) : Set (X dim)) volume)
    (fun _ _ => LocallyIntegrableOn.add) locallyIntegrableOn_zero h
  simpa only [← Finset.sum_apply] using this


theorem strong_form {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    {F : Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))}
    (heq : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient (Wkp.lowerOrder 1 V) x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), F x * φ x) :
    (fun x => ∑ i, ∑ k, a x i k * sd V i k x) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => -F x - ∑ i, ∑ k, fderiv ℝ (fun y => a y i k) x (EuclideanSpace.single i 1) *
        W1p.gradient (Wkp.lowerOrder 1 V) x k := by
  have hA := TangH2.contDiff_entry ha
  have hS : LocallyIntegrableOn (fun x => ∑ i, ∑ k,
      (fderiv ℝ (fun y => a y i k) x (EuclideanSpace.single i 1) *
        W1p.gradient (Wkp.lowerOrder 1 V) x k + a x i k * sd V i k x))
      ((fixedBallOpens dim) : Set (X dim)) volume :=
    li_sum _ fun i _ => li_sum _ fun k _ =>
      (TangH2.locallyIntegrableOn_mul (TangH2.contDiff_fderiv_apply (hA i k)
        (EuclideanSpace.single i 1)).continuous (li_W V k)).add
        (TangH2.locallyIntegrableOn_mul (hA i k).continuous (li_sd V i k))
  have hF : LocallyIntegrableOn (fun x => F x) ((fixedBallOpens dim) : Set (X dim)) volume :=
    TangH2.locallyIntegrableOn_of_memLp (Lp.memLp F)
  have hz := ae_zero_of_integral (hF.add hS) fun φ => by
    have h1 := (heq φ).symm.trans (integral_mbf_eq V ha φ)
    rw [setIntegral_test_eq, setIntegral_test_eq] at h1
    have i1 := integrable_test_mul hF φ
    have i2 := integrable_test_mul hS φ
    have h2 : ∫ x, φ x * ((fun x => F x) + fun x => ∑ i, ∑ k,
        (fderiv ℝ (fun y => a y i k) x (EuclideanSpace.single i 1) *
          W1p.gradient (Wkp.lowerOrder 1 V) x k + a x i k * sd V i k x)) x =
        (∫ x, F x * φ x) + ∫ x, (∑ i, ∑ k,
        (fderiv ℝ (fun y => a y i k) x (EuclideanSpace.single i 1) *
          W1p.gradient (Wkp.lowerOrder 1 V) x k + a x i k * sd V i k x)) * φ x := by
      rw [← integral_add (by simpa only [mul_comm] using i1) (by simpa only [mul_comm] using i2)]
      congr 1; funext x; simp only [Pi.add_apply]; ring
    rw [h2, h1]; ring
  filter_upwards [hz] with x hx
  simp only [Pi.add_apply, Pi.zero_apply, Finset.sum_add_distrib] at hx
  linarith

def ball34 (dim : ℕ) : Opens (X dim) := ⟨Metric.ball 0 (3 / 4), Metric.isOpen_ball⟩

lemma ball34_le : ball34 dim ≤ (fixedBallOpens dim) := by
  intro x hx
  change x ∈ Metric.ball (0 : (X dim)) (3 / 4) at hx
  change x ∈ Metric.ball (0 : (X dim)) 1
  rw [Metric.mem_ball] at hx ⊢; linarith

lemma mem_ball34 {x : (X dim)} : x ∈ (ball34 dim : Set (X dim)) ↔ ‖x‖ < 3 / 4 := by
  change x ∈ Metric.ball (0 : (X dim)) (3 / 4) ↔ _
  rw [Metric.mem_ball, dist_zero_right]


theorem sd_eq_zero
    (hv0 : ∀ᵐ x ∂(volume : Measure (X dim)).restrict (fixedBallOpens dim),
      ‖x‖ < 3 / 4 → W1p.value (Wkp.lowerOrder 1 V) x = 0) (i k : Fin dim) :
    ∀ᵐ x ∂(volume : Measure (X dim)).restrict (fixedBallOpens dim), ‖x‖ < 3 / 4 → sd V i k x = 0 := by
  have hm := (ball34 dim).isOpen.measurableSet
  have hval : ∀ᵐ x ∂(volume : Measure (X dim)).restrict (ball34 dim : Set (X dim)),
      W1p.value (Wkp.lowerOrder 1 V) x = 0 := by
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (show (ball34 dim : Set (X dim)) ⊆ (fixedBallOpens dim) from ball34_le) hv0
    filter_upwards [h1, ae_restrict_mem (μ := (volume : Measure (X dim))) hm] with x hx hxV
    exact hx (mem_ball34.mp hxV)
  have hg := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero ball34_le hval
  have hval2 : ∀ᵐ x ∂(volume : Measure (X dim)).restrict (ball34 dim : Set (X dim)),
      W1p.value (dv V k) x = 0 := by
    have h1 := ae_restrict_of_ae_restrict_of_subset
      (show (ball34 dim : Set (X dim)) ⊆ (fixedBallOpens dim) from ball34_le) (value_dv V k)
    filter_upwards [h1, hg] with x hx hgx
    rw [hx, hgx]; rfl
  have hg2 := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero ball34_le hval2
  rw [ae_restrict_iff' hm] at hg2
  refine ae_restrict_of_ae ?_
  filter_upwards [hg2] with x hx hxr
  simp only [sd, hx (mem_ball34.mpr hxr)]
  rfl


lemma hasWeakLineDerivOn_cW {c : (X dim) → ℝ} (hc : ContDiff ℝ ∞ c) (i k : Fin dim) :
    HasWeakLineDerivOn volume (fixedBallOpens dim)
      (fun x => c x * W1p.gradient (Wkp.lowerOrder 1 V) x k)
      (fun x => fderiv ℝ c x (TangH2.e i) * W1p.gradient (Wkp.lowerOrder 1 V) x k +
        c x * sd V i k x) (TangH2.e i) := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, TangH2.locallyIntegrableOn_mul hc.continuous (li_W V k),
    (TangH2.locallyIntegrableOn_mul (TangH2.contDiff_fderiv_apply hc _).continuous
      (li_W V k)).add (TangH2.locallyIntegrableOn_mul hc.continuous (li_sd V i k)),
    fun φ => ?_⟩
  simp only [smul_eq_mul]
  rw [ibp_ik V hc φ i k]
  congr 1; congr 1; funext x; ring

lemma fderiv_coord (j i : Fin dim) (x : (X dim)) :
    fderiv ℝ (fun y : (X dim) => y j) x (TangH2.e i) = if i = j then 1 else 0 := by
  have h : (fun y : (X dim) => y j) = ⇑(EuclideanSpace.proj j : (X dim) →L[ℝ] ℝ) := rfl
  rw [h, ContinuousLinearMap.fderiv]
  simp [TangH2.e, eq_comm]


theorem gradient_tangential {z : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2} (j k : Fin dim)
    (hz : ⇑(W1p.value z) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => x j * W1p.gradient (Wkp.lowerOrder 1 V) x k -
        x k * W1p.gradient (Wkp.lowerOrder 1 V) x j) (i : Fin dim) :
    (fun x => W1p.gradient z x i) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => (if i = j then W1p.gradient (Wkp.lowerOrder 1 V) x k else 0) + x j * sd V i k x -
        (if i = k then W1p.gradient (Wkp.lowerOrder 1 V) x j else 0) - x k * sd V i j x := by
  have H := (hasWeakLineDerivOn_cW V (TangH2.contDiff_coord j) i k).sub
    (hasWeakLineDerivOn_cW V (TangH2.contDiff_coord k) i j)
  have Hz : HasWeakLineDerivOn volume (fixedBallOpens dim) (W1p.value z) (fun x => W1p.gradient z x i)
      (TangH2.e i) := by
    refine ((W1p.hasWeakFDerivOn z) (TangH2.e i)).congr_ae_deriv
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [innerSL_apply_apply]
    rw [TangH2.coord_eq_inner]
  have H' := H.congr_ae (u := _) (w := ⇑(W1p.value z))
    (by filter_upwards [hz] with x hx; rw [hx]; rfl)
  filter_upwards [Hz.ae_eq H'] with x hx
  rw [hx]
  simp only [Pi.sub_apply, fderiv_coord]
  split_ifs <;> ring

end CalderonN.BallRegularity.SD
