module

public import Proof.CalderonN.MetricDivergence

import Proof.CalderonN.InteriorPointwise
import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.CrossTensor
import Proof.CalderonN.ProductDerivativeWords
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {d : ℕ} [NeZero d]

open Elliptic
open LocalMetricExtension (integral_sq_eq_norm_sq)

private theorem directionalWord_map_axis (w : List (I d)) (u : X d → ℝ) :
    directionalWord (w.map axis) u = wordDeriv w u := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, directionalWord, wordDeriv, ih]
    rfl

private theorem norm_multilinear_le_sum_coordinate {k : ℕ}
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin k => (X d)) ℝ)
    (C : (Fin k → (I d)) → ℝ) (hC : ∀ q, 0 ≤ C q)
    (hF : ∀ q, |F (fun j => axis (q j))| ≤ C q) :
    ‖F‖ ≤ ∑ q, C q := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun q _ => hC q)
  intro v
  let B := EuclideanSpace.basisFun (I d) ℝ
  let m (q : Fin k → (I d)) := ∏ j, B.repr (v j) (q j)
  have hv : v = fun j => ∑ i, B.repr (v j) i • B i :=
    funext fun j => (B.sum_repr (v j)).symm
  have hE : F v = ∑ q : Fin k → (I d), m q * F (fun j => axis (q j)) := by
    rw [hv,F.map_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [F.map_smul_univ,smul_eq_mul]
    simp only [m,B,EuclideanSpace.basisFun_apply,axis]
  have hM (q : Fin k → (I d)) : |m q| ≤ ∏ j, ‖v j‖ := by
    unfold m
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun j _ => abs_nonneg ((B.repr (v j)) (q j))) (fun j _ => ?_)
    rw [show B.repr (v j) (q j) = (v j) (q j) from rfl,← Real.norm_eq_abs]
    exact PiLp.norm_apply_le _ _
  rw [Real.norm_eq_abs,hE,Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [abs_mul,mul_comm (C q)]
  exact mul_le_mul (hM q) (hF q) (abs_nonneg _) (Finset.prod_nonneg fun j _ => norm_nonneg _)

private theorem lop_coeff_congr_germ {a b : (I d) → (I d) → (X d) → ℝ}
    {x : (X d)} (h : ∀ i j, a i j =ᶠ[𝓝 x] b i j) (u : (X d) → ℝ) :
    Lop a u x = Lop b u x := by
  unfold Lop
  refine Finset.sum_congr rfl fun i _ => pd_congr_of_eventuallyEq ?_ i
  filter_upwards [Filter.eventually_all.mpr (h i)] with y hy
  simp only [hy]

/-- Scalar interior derivative bounds in the actual chart (L²) norm,
with one constant for a compact metric family. -/
theorem exists_uniform_harmonic_interior_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J) {U : Set (X d)} (hU : IsOpen U)
    {g : P → (MetricField d)} (hg : ∀ p ∈ J, SmoothMetric U (g p))
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun q : P × (X d) => divergenceCoeff (g q.1) q.2 i j)
      ((univ : Set P) ×ˢ U))
    {K : Set (X d)} (hK : IsCompact K) (hKU : K ⊆ U) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J,
      ∀ (u : Lp ℝ 2 ((volume : Measure (X d)).restrict U)) (f : (X d) → ℝ), Harmonic U (g p) f →
        (u : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] f →
          ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖u‖ := by
  obtain ⟨V,hV,hKV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ζ,hζ,_,hζU,hζV⟩ := exists_plateau_cutoff hU hVc hVU
  let b (p : P) (i j : (I d)) (x : (X d)) := divergenceCoeff (g p) x i j
  let a (p : P) (i j : (I d)) (x : (X d)) := ζ x*b p i j x
  have ha (i j : (I d)) : Strict.JointSmooth (fun p => a p i j) := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q.2 ∈ U
    · exact (hζ.contDiffAt.comp q contDiffAt_snd).mul
        ((hA i j).contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hq⟩))
    · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      have hN := (isClosed_tsupport ζ).isOpen_compl.mem_nhds (fun hx => hq (hζU hx))
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hN] with z hz
      have he : ζ z.2 = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [a,he]
  have hζOne (x : (X d)) (hx : x ∈ V) : ζ =ᶠ[𝓝 x] fun _ => 1 := hζV x (subset_closure hx)
  have hpos (p : P) (hp : p ∈ J) (x : (X d)) (hx : x ∈ V) : Matrix.PosDef (fun i j => a p i j x : (Mat d)) := by
    have hxU := hVU (subset_closure hx)
    have hEq : (fun i j => a p i j x : (Mat d)) = chartVolume (g p) x • (g p x)⁻¹ := by
      ext i j
      simp [a,b,(hζOne x hx).eq_of_nhds,divergenceCoeff,Matrix.smul_apply,smul_eq_mul]
    rw [hEq]
    exact ((hg p hp).2 x hxU).inv.smul (Real.sqrt_pos.mpr ((hg p hp).2 x hxU).det_pos)
  choose A hAc hbound using (fun q : Fin k → (I d) =>
    exists_interior_word_point_bound_family hJ hV hK hKV a ha hpos (List.ofFn q))
  refine ⟨∑ q, A q,Finset.sum_nonneg fun q _ => hAc q,fun p hp u f hf hrep x hx => ?_⟩
  let F (y : (X d)) := ζ y*f y
  have hF : ContDiff ℝ ∞ F := contDiff_mul_of_tsupport_subset hU hζ hζU hf.1
  have hFeq (y : (X d)) (hy : y ∈ V) : F =ᶠ[𝓝 y] f :=
    (hζOne y hy).mono fun z hz => by simp [F,hz]
  have hAeq (y : (X d)) (hy : y ∈ V) (i j : (I d)) : a p i j =ᶠ[𝓝 y] b p i j :=
    (hζOne y hy).mono fun z hz => by simp [a,hz]
  have hPDE (y : (X d)) (hy : y ∈ V) : Lop (a p) F y = 0 := by
    have hyU := hVU (subset_closure hy)
    have hCoeff := lop_coeff_congr_germ (hAeq y hy) F
    rw [hCoeff]
    have hD (j : I d) : coordDeriv j F =ᶠ[𝓝 y] coordDeriv j f := by
      filter_upwards [(hFeq y hy).fderiv (𝕜 := ℝ)] with z hz
      exact congrFun (congrArg DFunLike.coe hz) (axis j)
    have hLop : Lop (b p) F y = Lop (b p) f y := by
      unfold Lop
      refine Finset.sum_congr rfl fun i _ => pd_congr_of_eventuallyEq ?_ i
      filter_upwards [Filter.eventually_all.mpr hD] with z hz
      simp only [Elliptic.pd, coordDeriv] at hz ⊢
      simp only [hz]
    rw [hLop]
    change (∑ i, coordDeriv i (fun z => divergenceFlux (g p) f z i) y) = 0
    rw [← chartVolume_mul_laplace_eq_divergence hU (hg p hp) hf.1 hyU, hf.2 y hyU, mul_zero]
  have hIntU : IntegrableOn (fun y => f y^2) U :=
    (Lp.memLp u).integrable_sq.congr (hrep.mono fun _ hy => congrArg (fun a : ℝ => a^2) hy)
  have hIntV : IntegrableOn (fun y => F y^2) V :=
    (hIntU.mono_set (subset_closure.trans hVU)).congr_fun
      (fun y hy => by rw [(hFeq y hy).eq_of_nhds]) hV.measurableSet
  have hInt : (∫ y in V, F y^2) ≤ ‖u‖^2 := by
    calc
      _ = ∫ y in V, f y^2 := setIntegral_congr_fun hV.measurableSet (fun y hy => by rw [(hFeq y hy).eq_of_nhds])
      _ ≤ ∫ y in U, f y^2 := setIntegral_mono_set hIntU (ae_of_all _ fun _ => sq_nonneg _)
        (subset_closure.trans hVU).eventuallyLE
      _ = ∫ y in U, (u y)^2 := integral_congr_ae (hrep.symm.mono fun _ hy => congrArg (fun a : ℝ => a^2) hy)
      _ = ‖u‖^2 := integral_sq_eq_norm_sq u
  have hFjet := (hFeq x (hKV hx)).iteratedFDeriv (𝕜 := ℝ) k
  rw [← hFjet.eq_of_nhds, Finset.sum_mul]
  apply norm_multilinear_le_sum_coordinate _ (fun q => A q * ‖u‖) (fun q => mul_nonneg (hAc q) (norm_nonneg _))
  intro q
  rw [← directionalWord_ofFn_eq_iteratedFDeriv hF]
  change |directionalWord (List.ofFn (axis ∘ q)) F x| ≤ _
  rw [← List.map_ofFn, directionalWord_map_axis]
  have he := Real.sqrt_le_sqrt hInt
  rw [Real.sqrt_sq (norm_nonneg _)] at he
  exact (hbound q p hp F hF hPDE hIntV x hx).trans (mul_le_mul_of_nonneg_left he (hAc q))

end CalderonN
