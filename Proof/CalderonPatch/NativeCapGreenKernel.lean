module

public import Proof.CalderonPatch.GreenColumnIntegrability
public import Proof.CalderonPatch.GreenKernelSmooth
public import Proof.CalderonPatch.GreenPoleLaplacianTests

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace CalderonPatch

open CalderonN (IsDirichletGreenKernel)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

variable {D : DirichletData m M} (h : NativeInverseRegularity D)

private def constantSource (r : ℝ) : Source := ⟨fun _ => r,contMDiff_const⟩

private def mulSource (f g : Source) : Source := by
  refine ⟨fun p => f p * g p, ?_⟩
  have hm : ContMDiff ((R).prod R) R ∞ (fun z : ℝ × ℝ => z.1 * z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (contDiff_fst.mul contDiff_snd).contMDiff
  exact hm.comp ((show ContMDiff J R ∞ (f : M → ℝ) from f.property).prodMk
    (show ContMDiff J R ∞ (g : M → ℝ) from g.property))

theorem integrable_nativeGreenCandidate_mul {q : M} (hq : q ∈ (J).interior M) (f : Source) :
    Integrable (fun p => nativeGreenCandidate h (p,q) * f p) D.volume := by
  have hf : Continuous (f : M → ℝ) := f.property.continuous
  obtain ⟨B,hB⟩ := hf.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  exact (integrable_nativeGreenCandidate h hq).mul_bdd hf.aestronglyMeasurable
    (Eventually.of_forall hB)

private def columnIntegral {q : M} (hq : q ∈ (J).interior M) : Source →ₗ[ℝ] ℝ where
  toFun f := ∫ x, nativeGreenCandidate h (x,q) * f x ∂D.volume
  map_add' f g := by
    change (∫ x, nativeGreenCandidate h (x,q) * (f x+g x) ∂D.volume) = _
    simp only [mul_add, integral_add (integrable_nativeGreenCandidate_mul h hq f)
      (integrable_nativeGreenCandidate_mul h hq g)]
  map_smul' r f := by
    change (∫ x, nativeGreenCandidate h (x,q) * (r*f x) ∂D.volume) = _
    simp only [mul_left_comm (nativeGreenCandidate h _),integral_const_mul,smul_eq_mul,
      RingHom.id_apply]

private def evaluationResidual {q : M} (hq : q ∈ (J).interior M) : Source →ₗ[ℝ] ℝ :=
  (LinearMap.proj q).comp (D.smoothInverseL h) - columnIntegral h hq

private theorem evaluationResidual_apply {q : M} (hq : q ∈ (J).interior M) (f : Source) :
    evaluationResidual h hq f = D.smoothInverse h f q -
      ∫ x, nativeGreenCandidate h (x,q) * f x ∂D.volume := by
  unfold evaluationResidual columnIntegral
  rfl

private theorem evaluationResidual_bound {q : M} (hq : q ∈ (J).interior M) (f : Source)
    {ε : ℝ} (hε : 0 ≤ ε) (hf : ∀ x, |f x| ≤ ε) :
    |evaluationResidual h hq f| ≤
      (D.smoothInverse h (constantSource (M := M) 1) q + ∫ x, nativeGreenCandidate h (x,q) ∂D.volume) * ε := by
  let one : Source := constantSource 1
  have hUpper := D.smoothInverse_mono h f (ε • one)
    (fun p => by
      change f p ≤ ε * 1
      rw [mul_one]
      exact (le_abs_self _).trans (hf p)) q
  have hLower := D.smoothInverse_mono h ((-ε) • one) f
    (fun p => by
      change (-ε) * 1 ≤ f p
      rw [mul_one]
      exact (abs_le.mp (hf p)).1) q
  rw [← D.smoothInverseL_apply h (ε • one), map_smul, Pi.smul_apply, smul_eq_mul,
    D.smoothInverseL_apply h one] at hUpper
  rw [← D.smoothInverseL_apply h ((-ε) • one), map_smul, Pi.smul_apply, smul_eq_mul,
    D.smoothInverseL_apply h one, neg_mul] at hLower
  have hA : |D.smoothInverse h f q| ≤ ε * D.smoothInverse h one q := by
    exact abs_le.mpr ⟨hLower,hUpper⟩
  have hInt : |∫ x, nativeGreenCandidate h (x,q) * f x ∂D.volume| ≤
      ε * ∫ x, nativeGreenCandidate h (x,q) ∂D.volume := by
    rw [← Real.norm_eq_abs,← integral_const_mul]
    apply norm_integral_le_of_norm_le ((integrable_nativeGreenCandidate h hq).const_mul ε)
    filter_upwards with x
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (nativeGreenCandidate_nonneg h hq x),mul_comm ε]
    exact mul_le_mul_of_nonneg_left (hf x) (nativeGreenCandidate_nonneg h hq x)
  rw [evaluationResidual_apply, sub_eq_add_neg]
  calc
    _ ≤ |D.smoothInverse h f q| + |∫ x, nativeGreenCandidate h (x,q) * f x ∂D.volume| := by
      simpa only [abs_neg] using abs_add_le (D.smoothInverse h f q)
        (-(∫ x, nativeGreenCandidate h (x,q) * f x ∂D.volume))
    _ ≤ ε * D.smoothInverse h one q + ε * ∫ x, nativeGreenCandidate h (x,q) ∂D.volume :=
      add_le_add hA hInt
    _ = _ := by dsimp [one]; ring

private theorem evaluationResidual_eq_zero_of_value_zero {q : M} (hq : q ∈ (J).interior M)
    (f : Source) (hfq : f q = 0) : evaluationResidual h hq f = 0 := by
  obtain ⟨N⟩ := GreenPole.exists_neighborhoods hq
  let c := D.smoothInverse h (constantSource (M := M) 1) q +
    ∫ x, nativeGreenCandidate h (x,q) ∂D.volume
  have hc : 0 ≤ c := add_nonneg (D.smoothInverse_nonneg h _ (fun _ => zero_le_one) q)
    (integral_nonneg (nativeGreenCandidate_nonneg h hq))
  by_contra hn
  have hR : 0 < |evaluationResidual h hq f| := abs_pos.mpr hn
  let ε := |evaluationResidual h hq f| / (c+1)
  have hε : 0 < ε := div_pos hR (by positivity)
  have hCont : Continuous (fun x => |f x|) := f.property.continuous.abs
  have hN := N.shrinking {x | |f x| < ε}
    (hCont.continuousAt.eventually (gt_mem_nhds (by simpa [hfq] using hε)))
  obtain ⟨n,hn⟩ := hN.exists
  let χ := N.cutoff n
  let a := mulSource f (constantSource 1 - χ)
  let b := mulSource f χ
  have hA : q ∉ tsupport (a : M → ℝ) := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [N.cutoff_one_near n] with x hx
    change f x * (1 - χ x) = 0
    rw [show χ x = 1 from hx,sub_self,mul_zero]
  have hZA : evaluationResidual h hq a = 0 := by
    rw [evaluationResidual_apply,(nativeGreenCandidate_integral_of_off_pole_source h hq a hA).2,sub_self]
  have he : f = a+b := by
    apply Subtype.ext
    funext x
    change f x = f x * (1-χ x) + f x * χ x
    ring
  have hR' : evaluationResidual h hq f = evaluationResidual h hq b := by
    conv_lhs => rw [he,map_add,hZA,zero_add]
  have hB (x : M) : |b x| ≤ ε := by
    change |f x * χ x| ≤ ε
    by_cases hx : x ∈ tsupport (χ : M → ℝ)
    · rw [abs_mul,abs_of_nonneg (N.cutoff_in_range n x).1]
      exact (mul_le_mul_of_nonneg_left (N.cutoff_in_range n x).2 (abs_nonneg _)).trans
        (by simpa only [mul_one] using (hn (N.cutoff_support n hx)).le)
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero,abs_zero]
      exact hε.le
  have hBound := evaluationResidual_bound h hq b hε.le hB
  rw [← hR'] at hBound
  change |evaluationResidual h hq f| ≤ c * ε at hBound
  have heps : ε * (c+1) = |evaluationResidual h hq f| :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

private theorem evaluationResidual_eq_mul_value {q : M} (hq : q ∈ (J).interior M) (f : Source) :
    evaluationResidual h hq f = f q * evaluationResidual h hq (constantSource 1) := by
  let one : Source := constantSource 1
  have h0 : (f - f q • one : Source) q = 0 := by
    change f q - f q * 1 = 0
    rw [mul_one,sub_self]
  have he := evaluationResidual_eq_zero_of_value_zero h hq (f - f q • one) h0
  rw [map_sub,map_smul,smul_eq_mul,sub_eq_zero] at he
  exact he

theorem smoothInverse_eq_dirichletTest_of_ae {f : Source} (v : DirichletTest D)
    (hf : (f : M → ℝ) =ᵐ[D.volume] -nativeLaplace D.metric (v : M → ℝ)) :
    D.smoothInverse h f = (v : M → ℝ) := by
  apply D.smoothInverse_unique h f v.smooth
  have hSource : D.smoothSourceToLp 2 f = D.positiveLaplaceLp v v.smooth :=
    Lp.ext ((D.smoothSourceToLp_ae 2 f).trans (hf.trans (D.positiveLaplaceLp_ae_eq v v.smooth).symm))
  rw [hSource,D.weakInverseL2_positiveLaplaceLp]
  exact D.testLp_ae_eq v

/-- The possible point mass in the evaluation functional vanishes
because uniformly bounded shrinking Laplacian tests retain a fixed
nonzero value at the pole. -/
private theorem evaluationResidual_eq_zero {q : M} (hq : q ∈ (J).interior M) :
    evaluationResidual h hq (constantSource 1) = 0 := by
  obtain ⟨v,f,B,hB,hF,hBound,hLim⟩ := GreenPole.exists_laplacianTests D hq
  let G (x : M) := nativeGreenCandidate h (x,q)
  let a := evaluationResidual h hq (constantSource 1)
  have hTest (n : ℕ) : D.smoothInverse h (f n) q = 0 := by
    rw [smoothInverse_eq_dirichletTest_of_ae h (v n) (Eventually.of_forall fun p => congrFun (hF n).2.2 p)]
    exact (hF n).1
  have hEq (n : ℕ) : (∫ p, G p * f n p ∂D.volume) = (m+1:ℝ)*a := by
    have he := evaluationResidual_eq_mul_value h hq (f n)
    rw [evaluationResidual_apply,hTest n,(hF n).2.1] at he
    change 0 - (∫ p, G p * f n p ∂D.volume) = -((m+1 : ℝ))*a at he
    linarith
  have hD := integrable_nativeGreenCandidate h hq
  have hAE : ∀ᵐ p ∂D.volume, p ≠ q := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using
      metricVolume_singleton_interior D.metric D.volume D.metric_volume hq
  have hT : Tendsto (fun n => ∫ p, G p * f n p ∂D.volume) atTop (𝓝 0) := by
    rw [← integral_zero (μ := D.volume) (G := ℝ)]
    apply tendsto_integral_of_dominated_convergence (fun p => B*|G p|)
    · exact fun n => (integrable_nativeGreenCandidate_mul h hq (f n)).aestronglyMeasurable
    · exact hD.abs.const_mul _
    · intro n
      filter_upwards with p
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,mul_comm B]
      exact mul_le_mul_of_nonneg_left (hBound n p) (abs_nonneg _)
    · filter_upwards [hAE] with p hp
      exact tendsto_const_nhds.congr' ((hLim p hp).mono fun n hn => by
        change (0 : ℝ) = G p * f n p
        rw [hn,mul_zero])
  have hz : (m+1 : ℝ)*a = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr (fun n => (hEq n).symm)) hT
  exact (mul_eq_zero.mp hz).resolve_left (by positivity)

theorem nativeGreenCandidate_inverse_representation {q : M} (hq : q ∈ (J).interior M)
    (f : Source) :
    (∫ p, nativeGreenCandidate h (p,q) * f p ∂D.volume) = D.smoothInverse h f q := by
  have he := evaluationResidual_eq_mul_value h hq f
  rw [evaluationResidual_eq_zero h hq,mul_zero,evaluationResidual_apply,sub_eq_zero] at he
  exact he.symm

/-- The actual canonical Dirichlet inverse has an integrable,
symmetric Green kernel with smooth off-diagonal representatives. -/
theorem exists_nativeCapGreenKernel (D : DirichletData m M) (h : NativeInverseRegularity D) :
    ∃ G : M × M → ℝ, IsDirichletGreenKernel J D.volume (nativeLaplace D.metric) G ∧
      ∀ q ∈ (J).interior M, ∀ f : Source,
        Integrable (fun p => G (p,q) * f p) D.volume ∧
        (∫ p, G (p,q) * f p ∂D.volume) = D.smoothInverse h f q := by
  refine ⟨nativeGreenCandidate h,
    ⟨nativeGreenCandidate_smooth_off_diagonal h,
      fun _ _ hx hy hne => nativeGreenCandidate_symmetric h hx hy hne,
      fun _ hq => nativeGreenCandidate_continuous_off_pole h hq,
      fun _ hx _ hq => nativeGreenCandidate_boundary_zero h hx hq,
      fun _ hq => integrable_nativeGreenCandidate h hq, ?_⟩,
    fun _ hq f => ⟨integrable_nativeGreenCandidate_mul h hq f,
      nativeGreenCandidate_inverse_representation h hq f⟩⟩
  intro q hq u hu _ hSupp
  let v : DirichletTest D := DirichletTest.ofSmooth u hu (fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hs =>
      (show x ∈ ((J).interior M)ᶜ by rw [(J).compl_interior]; exact hx) (hSupp hs)))
  obtain ⟨L,hL,hEq⟩ := exists_smooth_nativeLaplace D.metric hu
  let f : Source := ⟨-L,hL.neg⟩
  have hI : ∀ᵐ x ∂D.volume, x ∈ (J).interior M := by
    rw [ae_iff]
    change D.volume ((J).interior M)ᶜ = 0
    rw [(J).compl_interior]
    exact metricVolume_boundary_eq_zero D.metric D.volume D.metric_volume
  have hf : (f : M → ℝ) =ᵐ[D.volume] -nativeLaplace D.metric u :=
    hI.mono fun x hx => congrArg Neg.neg (hEq hx)
  have hMul := hf.mono fun x he => congrArg (fun a => nativeGreenCandidate h (x,q) * a) he
  refine ⟨(integrable_nativeGreenCandidate_mul h hq f).congr hMul,?_⟩
  calc
    _ = ∫ p, nativeGreenCandidate h (p,q) * f p ∂D.volume := by
      simpa only [Pi.neg_apply] using (integral_congr_ae hMul).symm
    _ = D.smoothInverse h f q := nativeGreenCandidate_inverse_representation h hq f
    _ = u q := congrFun (smoothInverse_eq_dirichletTest_of_ae h v hf) q

end CalderonPatch
