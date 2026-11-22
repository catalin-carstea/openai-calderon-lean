module

public import Proof.CalderonN.GreenWeak
public import Proof.CalderonN.MetricDivergence
public import Proof.CalderonN.EllipticCalculus
public import Mathlib.Analysis.Matrix.Normed

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Set

public section

/- Source cutoff commutator and Green testing identity from the 3D Theorem
   3.1 release. The symmetric mixed term is proved with finite-index sums. -/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN
open Elliptic
variable {n : ℕ}

@[expose] def negativeBallDivergence (a : X n → Mat n) (b : X n → ℝ) (x : X n) : ℝ :=
  -Lop (fun i j z => a z i j) b x

theorem contDiff_negativeBallDivergence {a : X n → Mat n} (ha : ContDiff ℝ ∞ a)
    {b : X n → ℝ} (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (negativeBallDivergence a b) := by
  have hA (i j : I n) : ContDiff ℝ ∞ (fun z => a z i j) :=
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.comp ha
  exact (ContDiff.sum fun i _ => contDiff_pd
    (ContDiff.sum fun j _ => (hA i j).mul (contDiff_pd hb))).neg

private theorem lop_mul_symm (a : I n → I n → X n → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    {χ b : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hb : ContDiff ℝ ∞ b) (x : X n)
    (hs : ∀ i j, a i j x = a j i x) :
    Lop a (fun z => χ z * b z) x = χ x * Lop a b x + b x * Lop a χ x +
      2 * ∑ i, ∑ j, a i j x * pd i χ x * pd j b x := by
  let G (i : I n) (z : X n) := ∑ j, a i j z * pd j b z
  let H (i : I n) (z : X n) := ∑ j, a i j z * pd j χ z
  have hG (i : I n) : ContDiff ℝ ∞ (G i) :=
    ContDiff.sum fun j _ => (ha i j).mul (contDiff_pd hb)
  have hH (i : I n) : ContDiff ℝ ∞ (H i) :=
    ContDiff.sum fun j _ => (ha i j).mul (contDiff_pd hχ)
  have hrow (i : I n) :
      (fun z => ∑ j, a i j z * pd j (fun w => χ w * b w) z) =
        fun z => χ z * G i z + b z * H i z := by
    funext z
    simp only [G, H, pd_mul hχ hb, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hGsum : (∑ i, pd i χ x * G i x) =
      ∑ i, ∑ j, a i j x * pd i χ x * pd j b x := by
    simp only [G, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hHsum : (∑ i, pd i b x * H i x) =
      ∑ i, ∑ j, a i j x * pd i χ x * pd j b x := by
    simp only [H, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun i j => pd i b x * (a i j x * pd j χ x))]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hs j i]
      ring
  simp_rw [Lop, hrow, pd_add (hχ.mul (hG _)) (hb.mul (hH _)),
    pd_mul hχ (hG _), pd_mul hb (hH _), Finset.sum_add_distrib, ← Finset.mul_sum, hGsum, hHsum]
  change _ = χ x * (∑ i, pd i (G i) x) + b x * (∑ i, pd i (H i) x) + _
  ring

/-- Terms from differentiating a fixed cutoff once or twice in the
divergence equation. -/
@[expose] def greenSourceCutoffError (a : (X n) → (Mat n)) (χ b : (X n) → ℝ) (x : (X n)) : ℝ :=
  b x * negativeBallDivergence a χ x -
    2 * ∑ i, ∑ j, a x i j * coordDeriv i χ x * coordDeriv j b x

theorem negativeBallDivergence_mul_eq_at_symm
    {a : (X n) → (Mat n)} (ha : ContDiff ℝ ∞ a)
    {χ b : (X n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hb : ContDiff ℝ ∞ b) (x : (X n))
    (hs : ∀ i j, a x i j = a x j i) :
    negativeBallDivergence a (fun z => χ z * b z) x =
      χ x * negativeBallDivergence a b x + greenSourceCutoffError a χ b x := by
  let A (i j : (I n)) (x : (X n)) := a x i j
  have hA (i j : (I n)) : ContDiff ℝ ∞ (A i j) :=
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.comp ha
  change -Lop A (fun z => χ z * b z) x =
    χ x * (-Lop A b x) + (b x * (-Lop A χ x) -
      2 * ∑ i, ∑ j, A i j x * pd i χ x * pd j b x)
  rw [lop_mul_symm A hA hχ hb x hs]
  ring

theorem negativeBallDivergence_mul_eq
    {a : (X n) → (Mat n)} (ha : ContDiff ℝ ∞ a) (hs : ∀ i j x, a x i j = a x j i)
    {χ b : (X n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hb : ContDiff ℝ ∞ b) (x : (X n)) :
    negativeBallDivergence a (fun z => χ z * b z) x =
      χ x * negativeBallDivergence a b x + greenSourceCutoffError a χ b x :=
  negativeBallDivergence_mul_eq_at_symm ha hχ hb x (fun i j => hs i j x)

theorem negativeBallDivergence_congr_germ {a c : (X n) → (Mat n)} {b d : (X n) → ℝ} {x : (X n)}
    (ha : a =ᶠ[𝓝 x] c) (hb : b =ᶠ[𝓝 x] d) :
    negativeBallDivergence a b x = negativeBallDivergence c d x := by
  have hD (j : (I n)) : coordDeriv j b =ᶠ[𝓝 x] coordDeriv j d :=
    hb.fderiv.mono (fun _ hz => congrArg (fun k : (X n) →L[ℝ] ℝ => k (axis j)) hz)
  unfold negativeBallDivergence
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply pd_congr_of_eventuallyEq _ i
  filter_upwards [ha,eventually_all.mpr hD] with z hz hz'
  simp only [hz,hz']

theorem greenSourceCutoffError_eq_zero
    {a : (X n) → (Mat n)} {χ b : (X n) → ℝ} {x : (X n)} {t : ℝ}
    (h : χ =ᶠ[𝓝 x] fun _ => t) : greenSourceCutoffError a χ b x = 0 := by
  have hd := negativeBallDivergence_congr_germ (EventuallyEq.rfl (f := a)) h
  have hD (i : (I n)) : coordDeriv i χ x = 0 := by
    unfold coordDeriv
    rw [h.fderiv_eq]
    simp
  have hn : negativeBallDivergence a (fun _ => t) x = 0 := by
    simp [negativeBallDivergence, Lop, pd_const]
  simp [greenSourceCutoffError,hd,hn,hD]

theorem negativeBallDivergence_eq_neg_laplace_density
    {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : (MetricField n)} (hg : SmoothMetric Ω g)
    {a : (X n) → (Mat n)} {u : (X n) → ℝ} (hu : ContDiff ℝ ∞ u) {x : (X n)} (hx : x ∈ Ω)
    (ha : a =ᶠ[𝓝 x] fun z => (fun i j => divergenceCoeff g z i j : (Mat n))) :
    negativeBallDivergence a u x = -laplace g u x * chartVolume g x := by
  rw [negativeBallDivergence_congr_germ ha EventuallyEq.rfl]
  change -(∑ i, coordDeriv i (fun z => divergenceFlux g u z i) x) = _
  rw [← chartVolume_mul_laplace_eq_divergence hΩ hg hu.contDiffOn hx]
  ring

theorem contDiff_greenSourceCutoffError
    {a : (X n) → (Mat n)} (ha : ContDiff ℝ ∞ a)
    {χ b : (X n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (greenSourceCutoffError a χ b) := by
  have hA (i j : (I n)) : ContDiff ℝ ∞ (fun z => a z i j) :=
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.comp ha
  have hD {u : (X n) → ℝ} (hu : ContDiff ℝ ∞ u) (i : (I n)) : ContDiff ℝ ∞ (coordDeriv i u) :=
    (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact (hb.mul (contDiff_negativeBallDivergence ha hχ)).sub
    (contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      ((hA i j).mul (hD hχ i)).mul (hD hb j)))

theorem exists_cutoffError_pointwise_bound
    {K : Set (X n)} (hK : IsCompact K) {a : (X n) → (Mat n)} (ha : ContDiff ℝ ∞ a)
    {χ : (X n) → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : (X n) → ℝ) (x : (X n)), x ∈ K →
      |greenSourceCutoffError a χ b x| ≤ C * (|b x| + ‖fderiv ℝ b x‖) := by
  let M (x : (X n)) := |negativeBallDivergence a χ x| +
    2 * ∑ i, ∑ j, |a x i j * coordDeriv i χ x|
  have hA (i j : (I n)) : Continuous (fun z => a z i j) :=
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).continuous.comp ha.continuous
  have hχ' (i : (I n)) : Continuous (coordDeriv i χ) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hM : Continuous M := (contDiff_negativeBallDivergence ha hχ).continuous.abs.add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hA i j).mul (hχ' i)).abs))
  obtain ⟨C,hC⟩ := hK.bddAbove_image hM.continuousOn
  refine ⟨max C 0,le_max_right _ _,fun b x hx => ?_⟩
  have hk : M x ≤ max C 0 := (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hD (j : (I n)) : |coordDeriv j b x| ≤ ‖fderiv ℝ b x‖ := by
    have h := (fderiv ℝ b x).le_opNorm (axis j)
    simpa [coordDeriv,axis,Real.norm_eq_abs] using h
  have hSum : |∑ i, ∑ j, a x i j * coordDeriv i χ x * coordDeriv j b x| ≤
      (∑ i, ∑ j, |a x i j * coordDeriv i χ x|) * ‖fderiv ℝ b x‖ := by
    rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_mul]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hD j) (abs_nonneg _)
  rw [greenSourceCutoffError]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hSum two_pos.le)).trans ?_
  have hN₁ : 0 ≤ |negativeBallDivergence a χ x| := abs_nonneg _
  have hN₂ : 0 ≤ ∑ i, ∑ j, |a x i j * coordDeriv i χ x| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  calc
    _ ≤ M x * (|b x| + ‖fderiv ℝ b x‖) := by
      dsimp only [M]
      nlinarith only [mul_nonneg hN₁ (norm_nonneg (fderiv ℝ b x)),
        mul_nonneg hN₂ (abs_nonneg (b x))]
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (add_nonneg (abs_nonneg _) (norm_nonneg _))

/-- The localized Green law with a fixed cutoff replaces a compact
source by its solution value and a commutator on the cutoff annulus. -/
theorem green_cutoff_source_identity
    {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : (MetricField n)} (hg : SmoothMetric Ω g)
    {G : (X n) × (X n) → ℝ} (hG : GreenGerm Ω g G) {y : (X n)} (hy : y ∈ Ω)
    {B : Set (X n)} (hB : IsOpen B) (hBΩ : B ⊆ Ω)
    {a : (X n) → (Mat n)} (ha : ContDiff ℝ ∞ a) (hs : ∀ i j x, a x i j = a x j i)
    (haG : EqOn a (fun z => (fun i j => divergenceCoeff g z i j : (Mat n))) B)
    {χ b f : (X n) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχB : tsupport χ ⊆ B)
    (hχy : χ y = 1) (hχf : EqOn χ (fun _ => 1) (Function.support f))
    (hb : ContDiff ℝ ∞ b) (hbEq : EqOn (negativeBallDivergence a b) f (tsupport χ))
    (hSource : IntegrableOn (fun x => G (x,y) * f x) B)
    (hError : IntegrableOn (fun x => G (x,y) * greenSourceCutoffError a χ b x) B) :
    (∫ x in B, G (x,y) * f x) =
      b y - ∫ x in B, G (x,y) * greenSourceCutoffError a χ b x := by
  let u (x : (X n)) := χ x*b x
  have hu : ContDiff ℝ ∞ u := hχ.mul hb
  have huSupp : tsupport u ⊆ tsupport χ := tsupport_mul_subset_left
  have huc : HasCompactSupport u := hχc.mono (fun x hx => by
    intro hz
    exact hx (by simp [u,show χ x = 0 from hz]))
  have hLaw := ((hG.2.2 y hy).2 u hu huc (huSupp.trans (hχB.trans hBΩ)))
  change (∫ x in Ω, G (x,y) * (-laplace g u x) * chartVolume g x) = χ y*b y at hLaw
  rw [hχy,one_mul] at hLaw
  have hRestrict : (∫ x in Ω, G (x,y) * (-laplace g u x) * chartVolume g x) =
      ∫ x in B, G (x,y) * (-laplace g u x) * chartVolume g x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hΩ.measurableSet hBΩ
    intro x hx
    have hxU : x ∉ tsupport u := fun ht => hx.2 (hχB (huSupp ht))
    have hzero : laplace g u x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hxU (tsupport_laplace_subset g u ht))
    simp [hzero]
  rw [hRestrict] at hLaw
  have hFn (x : (X n)) (hx : x ∈ B) :
      G (x,y) * (-laplace g u x) * chartVolume g x =
        G (x,y)*f x + G (x,y)*greenSourceCutoffError a χ b x := by
    have ha' : a =ᶠ[𝓝 x] fun z => (fun i j => divergenceCoeff g z i j : (Mat n)) :=
      Filter.mem_of_superset (hB.mem_nhds hx) (fun z hz => haG hz)
    have hEq := negativeBallDivergence_eq_neg_laplace_density hΩ hg hu (hBΩ hx) ha'
    rw [mul_assoc, ← hEq, negativeBallDivergence_mul_eq ha hs hχ hb, mul_add]
    have hbf : χ x * negativeBallDivergence a b x = χ x * f x := by
      by_cases h : x ∈ tsupport χ
      · rw [hbEq h]
      · simp [image_eq_zero_of_notMem_tsupport h]
    rw [hbf]
    have hf : χ x*f x = f x := by
      by_cases h : x ∈ Function.support f
      · rw [hχf h,one_mul]
      · simp only [Function.notMem_support.mp h,mul_zero]
    rw [hf]
  rw [setIntegral_congr_fun hB.measurableSet hFn,integral_add hSource hError] at hLaw
  linarith

end CalderonN
