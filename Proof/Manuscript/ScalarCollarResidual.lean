module

public import Proof.Manuscript.ScalarCollarInterpolation
public import Proof.Manuscript.NumericConcaveCarleman

import Proof.CalderonN.CutoffCommutator
import Proof.CalderonN.InteriorJetCutoff
import Proof.CalderonN.CoordinateJets
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ContDiff Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

open CalderonN.Elliptic.Strict (JointSmooth jointSmooth_Lop jointSmooth_slice)

private def cutoffZ (L : ScalarElliptic n) (χ : X n → ℝ) (x : X n) : ℝ :=
  Elliptic.Lop (fun i j y => divergenceCoeff L.metric y i j) χ x +
    ∑ i, L.weightedDrift i x * coordDeriv i χ x

private def cutoffA (L : ScalarElliptic n) (χ : X n → ℝ) (i j : I n) (x : X n) : ℝ :=
  divergenceCoeff L.metric x i j * coordDeriv i χ x

set_option maxHeartbeats 1100000 in
private theorem cutoffZ_joint {L : ℝ → ScalarElliptic n} (hL : SmoothFamilyOn L univ)
    {χ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => cutoffZ (L q.1) χ q.2) := by
  have hP := jointSmooth_Lop
    (a := fun t i j x => divergenceCoeff (L t).metric x i j)
    (fun i j => hL.contDiff_divergence_univ i j)
    (f := fun _ => χ) (hχ.comp contDiff_snd)
  exact hP.add (ContDiff.sum fun i _ => (hL.contDiff_weightedDrift_univ i).mul
    ((Elliptic.contDiff_pd (i := i) hχ).comp contDiff_snd))

private theorem cutoffA_joint {L : ℝ → ScalarElliptic n} (hL : SmoothFamilyOn L univ)
    {χ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) (i j : I n) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => cutoffA (L q.1) χ i j q.2) :=
  (hL.contDiff_divergence_univ i j).mul ((Elliptic.contDiff_pd (i := i) hχ).comp contDiff_snd)

private theorem cutoff_formula_global {L : ScalarElliptic n} (hL : L.SmoothOn univ)
    {χ w : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hw : ContDiff ℝ ∞ w) (x : X n) :
    chartVolume L.metric x * L.apply (fun y => χ y * w y) x =
      χ x * (chartVolume L.metric x * L.apply w x) +
      cutoffZ L χ x * w x + 2 * ∑ i, ∑ j, cutoffA L χ i j x * coordDeriv j w x := by
  let a (i j : I n) (x : X n) := divergenceCoeff L.metric x i j
  have ha (i j : I n) : ContDiff ℝ ∞ (a i j) := contDiffOn_univ.mp (contDiffOn_divergenceCoeff hL.1 i j)
  have hs (i j : I n) (x : X n) : a i j x = a j i x :=
    divergenceCoeff_symm hL.1 (mem_univ x) i j
  rw [volume_mul_apply_eq isOpen_univ hL ((hχ.mul hw).contDiffOn) (mem_univ x),
    volume_mul_apply_eq isOpen_univ hL hw.contDiffOn (mem_univ x)]
  rw [Elliptic.CutoffCommutator.Lop_mul_symm a ha hs hχ hw x]
  simp only [cutoffZ,cutoffA,lowerOrder, ← show Elliptic.pd = (coordDeriv (n := n)) from rfl,
    Elliptic.pd_mul hχ hw, mul_add,Finset.sum_add_distrib,add_mul]
  simp only [Finset.mul_sum,Finset.sum_mul,a]
  ring

private theorem cutoff_formula_local {L : ScalarElliptic n} (hL : L.SmoothOn univ)
    {D : Set (X n)} (hD : IsOpen D) {χ w : X n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hw : L.SolvesOn D w) {x : X n} (hx : x ∈ D) :
    chartVolume L.metric x * L.apply (fun y => χ y * w y) x =
      cutoffZ L χ x * w x + 2 * ∑ i, ∑ j, cutoffA L χ i j x * coordDeriv j w x := by
  obtain ⟨ζ,hζ,_,hζD,hζx⟩ := Elliptic.exists_plateau_cutoff hD (isCompact_singleton (x := x))
    (singleton_subset_iff.mpr hx)
  let u (y : X n) := ζ y*w y
  have hu : ContDiff ℝ ∞ u := Elliptic.contDiff_mul_of_tsupport_subset hD hζ hζD hw.1
  have he : u =ᶠ[𝓝 x] w :=
    (hζx x (mem_singleton x)).mono fun y hy => by simp only [u,hy,one_mul]
  have hχe : (fun y => χ y*u y) =ᶠ[𝓝 x] (fun y => χ y*w y) :=
    he.mono fun y hy => congrArg (χ y * ·) hy
  have hder (i : I n) : coordDeriv i u x = coordDeriv i w x :=
    congrArg (fun T : X n →L[ℝ] ℝ => T (axis i)) he.fderiv_eq
  have h := cutoff_formula_global hL hχ hu x
  simpa only [apply_congr_of_eventuallyEq hχe,apply_congr_of_eventuallyEq he,he.eq_of_nhds,
    hder,hw.2 x hx,mul_zero,zero_add] using h

set_option maxHeartbeats 3000000 in
/-- Compact scalar cutoff residual bound. All constants are chosen from
the reference chart operator and the fixed cutoff and collar. -/
theorem exists_reference_scalar_collar_residual {L₀ : ScalarElliptic n}
    (h₀ : L₀.SmoothOn univ) {D S B : Set (X n)}
    (hD : IsOpen D) (hS : IsOpen S) (hSD : S ⊆ D) (hB : IsCompact B) (hBS : B ⊆ S)
    {χ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ → ScalarElliptic n, SmoothFamilyOn L univ → L 0 = L₀ →
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ w, (L t).SolvesOn D w → MemLp w 2 ((volume : Measure (X n)).restrict S) →
        (∫ x in B, (chartVolume (L t).metric x * (L t).apply (fun y => χ y*w y) x)^2) ≤
          C * ∫ x in S, w x^2 := by
  obtain ⟨W,hW,hBW,hWS,hWc⟩ := exists_open_between_and_isCompact_closure hB hS hBS
  let N := (fullCoordinateWord (n+3)).length + 1 + 2
  obtain ⟨a,A,ha,hA,hCoeff⟩ := exists_reference_scalar_coefficient_budget hWc h₀ N
  obtain ⟨C₀,hC₀,hJet₀⟩ := exists_numeric_scalar_interior_jet_bound hW hB hBW 0 ha hA
  obtain ⟨C₁,hC₁,hJet₁⟩ := exists_numeric_scalar_interior_jet_bound hW hB hBW 1 ha hA
  let J := (I n × I n) ⊕ Unit
  let F (L : ScalarElliptic n) (j : J) := Sum.elim (fun ij => cutoffA L χ ij.1 ij.2) (fun _ => cutoffZ L χ) j
  have hF (L : ℝ → ScalarElliptic n) (hL : SmoothFamilyOn L univ) (j : J) :
      ContDiff ℝ ∞ (fun q : ℝ × X n => F (L q.1) j q.2) := by
    cases j with
    | inl ij => exact cutoffA_joint hL hχ ij.1 ij.2
    | inr _ => exact cutoffZ_joint hL hχ
  have hF₀ (j : J) : ContDiff ℝ ∞ (F L₀ j) :=
    (hF (fun _ => L₀) (smoothFamilyOn_const h₀) j).comp
      ((contDiff_const (c := (0 : ℝ))).prodMk (contDiff_id : ContDiff ℝ ∞ (id : X n → X n)))
  obtain ⟨P,hP,hWeight⟩ := exists_reference_spatial_jet_bounds hB hF₀ 0
  let Mass := P*C₀ + 2*(n:ℝ)*(n:ℝ)*P*C₁
  have hMass : 0 ≤ Mass := by dsimp [Mass]; positivity
  let C := (volume : Measure (X n)).real B * Mass^2
  refine ⟨C,mul_nonneg measureReal_nonneg (sq_nonneg _),fun L hL he => ?_⟩
  filter_upwards [hCoeff L hL he, hWeight (fun j q => F (L q.1) j q.2) (hF L hL)
    (fun j => by change (fun x => F (L 0) j x) = F L₀ j; rw [he])] with t ht hPbound w hw hMem
  have hWsub : W ⊆ S := subset_closure.trans hWS
  have hWsubD : W ⊆ D := hWsub.trans hSD
  have hMemW := hMem.mono_measure (Measure.restrict_mono_set volume hWsub)
  let q := hMemW.toLp w
  have hq : (q : X n → ℝ) =ᵐ[volume.restrict W] w := hMemW.coeFn_toLp
  have hnW : ‖q‖ = lpNorm w 2 ((volume : Measure (X n)).restrict W) := Lp.norm_toLp _ _
  have hSolW : (L t).SolvesOn W w := ⟨hw.1.mono hWsubD,fun x hx => hw.2 x (hWsubD hx)⟩
  have hV (x : X n) (hx : x ∈ B) : |w x| ≤ C₀*‖q‖ := by
    have hJ := hJet₀ (L t) ((hL.1 t).restrict (subset_univ _))
      (ht.mono subset_closure (by dsimp [N]; omega)) q hSolW hq x hx
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hJ
  have hD (x : X n) (hx : x ∈ B) (i : I n) : |coordDeriv i w x| ≤ C₁*‖q‖ := by
    have hJ := hJet₁ (L t) ((hL.1 t).restrict (subset_univ _))
      (ht.mono subset_closure (by dsimp [N]; omega)) q hSolW hq x hx
    rw [norm_iteratedFDeriv_one] at hJ
    exact (by simpa only [coordDeriv,Real.norm_eq_abs,norm_axis,mul_one] using
      (fderiv ℝ w x).le_opNorm (axis i) : |coordDeriv i w x| ≤ ‖fderiv ℝ w x‖).trans hJ
  let R (x : X n) := chartVolume (L t).metric x * (L t).apply (fun y => χ y*w y) x
  have hPt (x : X n) (hx : x ∈ B) : |R x| ≤ Mass*‖q‖ := by
    have hK (i j : I n) : |cutoffA (L t) χ i j x| ≤ P := by
      simpa only [F,Sum.elim_inl,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
        hPbound x hx (Sum.inl (i,j)) 0 le_rfl
    have hZ : |cutoffZ (L t) χ x| ≤ P := by
      simpa only [F,Sum.elim_inr,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
        hPbound x hx (Sum.inr ()) 0 le_rfl
    have hsum : |∑ i, ∑ j, cutoffA (L t) χ i j x * coordDeriv j w x| ≤
        (n:ℝ)*(n:ℝ)*(P*(C₁*‖q‖)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ _ : I n, ∑ _ : I n, P*(C₁*‖q‖) := by
          apply Finset.sum_le_sum
          intro i _
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul (hK i j) (hD x hx j) (abs_nonneg _) hP.le
        _ = _ := by simp [mul_assoc]
    rw [show R x = _ from cutoff_formula_local (hL.1 t) (by exact ‹IsOpen D›) hχ hw (hSD (hBS hx))]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    exact (add_le_add (mul_le_mul hZ (hV x hx) (abs_nonneg _) hP.le)
      (mul_le_mul_of_nonneg_left hsum (by norm_num))).trans_eq (by dsimp [Mass]; ring)
  have hRcont : ContinuousOn R D := by
    have hRform : EqOn R (fun x => cutoffZ (L t) χ x * w x +
        2 * ∑ i, ∑ j, cutoffA (L t) χ i j x * coordDeriv j w x) D :=
      fun x hx => cutoff_formula_local (hL.1 t) (by exact ‹IsOpen D›) hχ hw hx
    have hcont (i j : I n) := (jointSmooth_slice (F := fun t => cutoffA (L t) χ i j)
      (cutoffA_joint hL hχ i j) t).continuous
    have hcontZ := (jointSmooth_slice (F := fun t => cutoffZ (L t) χ) (cutoffZ_joint hL hχ) t).continuous
    exact ((hcontZ.continuousOn.mul hw.1.continuousOn).add
      (continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
        (hcont i j).continuousOn.mul (contDiffOn_coordDeriv hw.1 (by exact ‹IsOpen D›) j).continuousOn))).congr hRform
  have hRint : IntegrableOn (fun x => R x ^ 2) B :=
    ((hRcont.mono (hBS.trans hSD)).pow 2).integrableOn_compact hB
  have hMInt : IntegrableOn (fun _ : X n => (Mass*‖q‖)^2) B :=
    continuousOn_const.integrableOn_compact hB
  have hInt := integral_mono_ae hRint hMInt
    ((ae_restrict_mem hB.measurableSet).mono (fun x hx => (sq_abs (R x)).symm.trans_le
      (pow_le_pow_left₀ (abs_nonneg _) (hPt x hx) 2)))
  rw [setIntegral_const,smul_eq_mul,mul_pow,← mul_assoc] at hInt
  have hNorm : ‖q‖^2 ≤ ∫ x in S, w x^2 := by
    rw [hnW,← memLp_integral_sq_eq_lpNorm_sq hMemW]
    exact setIntegral_mono_set hMem.integrable_sq (ae_of_all _ fun _ => sq_nonneg _) hWsub.eventuallyLE
  exact hInt.trans (mul_le_mul_of_nonneg_left hNorm (mul_nonneg measureReal_nonneg (sq_nonneg _)))

end CalderonPaper.ScalarElliptic
