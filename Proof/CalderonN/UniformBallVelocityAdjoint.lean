module

public import Proof.CalderonN.ParametricBallVelocityAdjoint
public import Proof.CalderonN.UniformBallConormalDifference

import Proof.CalderonN.FixedBallPoissonCongruence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! Adapted from `UniformBallVelocityAdjoint` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 6500000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

private theorem norm_angular_iteratedFDeriv_of_frozen_parameter {f : (X dim) → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : P) (w : (X dim)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q : P × (X dim) => f q.2) (p,w)‖ ≤ ‖iteratedFDeriv ℝ n f w‖ := by
  let L := ContinuousLinearMap.snd ℝ P (X dim)
  change ‖iteratedFDeriv ℝ n (f ∘ L) (p,w)‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf (p,w) (by simp)]
  have he : L (p,w) = w := rfl
  rw [he]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun x => by change ‖x.2‖ ≤ 1 * ‖x‖; rw [one_mul]; exact norm_snd_le x)
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL))

/-- A fixed number of angular derivatives of a real datum control its fixed-ball
velocity adjoint, uniformly for a compact metric and velocity family. -/
theorem exists_uniform_ballVelocityAdjoint_bound
    {U : Set (P × (X dim))} (hU : IsOpen U) {J : Set P} (hJ : IsCompact J)
    (hJU : J ×ˢ closedBall (0 : (X dim)) 1 ⊆ U)
    {g : P × (X dim) → (Mat dim)} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef)
    {V : P × (X dim) → (X dim)} (hV : ContDiffOn ℝ ∞ V U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ f : (X dim) → ℝ, ContDiff ℝ ∞ f →
      ∀ M : ℝ, 0 ≤ M →
      (∀ w ∈ (standardSphere dim), ∀ k ≤ dim+4, ‖iteratedFDeriv ℝ k f w‖ ≤ M) →
      ∀ w ∈ (standardSphere dim), ‖parametricBallVelocityAdjoint g V (fun q => f q.2) (p,w)‖ ≤ C*M := by
  let S := (standardSphere dim)
  have hS : IsCompact S := isCompact_sphere _ _
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  have hSN : S ⊆ N := by
    intro w hw
    show w ≠ 0
    intro he
    have h := mem_sphere_zero_iff_norm.mp hw
    simp [he] at h
  have hJs : J ×ˢ S ⊆ U := (Set.prod_mono (Subset.refl _) sphere_subset_closedBall).trans hJU
  let W := U ∩ (univ ×ˢ N)
  have hW : IsOpen W := hU.inter (isOpen_univ.prod hN)
  have hJW : J ×ˢ S ⊆ W := fun q hq => ⟨hJs hq,mem_univ _,hSN hq.2⟩
  let c (q : P × (X dim)) := conormalComponent (fun z => g (q.1,z)) q.2 (V q)
  let a (q : P × (X dim)) := ballConormalVector (fun z => g (q.1,z)) q.2
  let t (i j : (I dim)) (q : P × (X dim)) :=
    q.2 i * tangentialComponent (fun z => g (q.1,z)) q.2 (V q) j
  have ha : ContDiffOn ℝ ∞ a W := (contDiffOn_product_ballConormalVector hg hPos).mono inter_subset_left
  have hc : ContDiffOn ℝ ∞ c W :=
    (contDiff_snd.contDiffOn.inner ℝ (hV.mono inter_subset_left)).div
      (contDiff_snd.contDiffOn.inner ℝ ha) (fun q hq =>
        (ballConormalVector_inner_pos (hPos q hq.1) hq.2.2).ne')
  have ht (i j : (I dim)) : ContDiffOn ℝ ∞ (t i j) W := by
    have h := (hV.mono inter_subset_left).sub (hc.smul ha)
    exact (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd).contDiffOn).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn h)
  obtain ⟨c₀,hc₀,_,W₀,hW₀,hJW₀,_,hCeq⟩ := exists_contDiff_extension_near_compact hW (hJ.prod hS) hJW hc
  have hT (i j : (I dim)) := exists_contDiff_extension_near_compact hW (hJ.prod hS) hJW (ht i j)
  choose t₀ ht₀ _ W₁ hW₁ hJW₁ _ hTeq using hT
  obtain ⟨A,hA,hAjet⟩ := exists_uniform_finite_jet_bound (hJ.prod hS) hc₀ (dim+4)
  have hTjet (i j : (I dim)) := exists_uniform_finite_jet_bound (hJ.prod hS) (ht₀ i j) 1
  choose T hT₁ hTjet using hTjet
  obtain ⟨B₀,hB₀⟩ := (hJ.prod hS).exists_bound_of_continuousOn (ha.continuousOn.mono hJW)
  let B := max 0 B₀
  have hB : 0 ≤ B := le_max_left _ _
  have hBnd (q : P × (X dim)) (hq : q ∈ J ×ˢ S) : ‖a q‖ ≤ B :=
    (hB₀ q hq).trans (le_max_right _ _)
  obtain ⟨D,hD,hDCon⟩ := exists_uniform_ballConormalDifference_jets 0 1 zero_le_one hU hJ hJU hg hPos
  have hRot (i j : (I dim)) : Continuous (rotationVector i j : (X dim) → (X dim)) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.smul continuous_const).sub
      ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.smul continuous_const))
  have hRotB (i j : (I dim)) := hS.exists_bound_of_continuousOn (hRot i j).continuousOn
  choose L hL using hRotB
  let C := (D+B)*((2:ℝ)^(dim+4)*A) + ∑ i : (I dim), ∑ j : (I dim), 2*T i j * max 0 (L i j)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans (hT₁ i j))) (le_max_left _ _))
  refine ⟨C,hC,?_⟩
  intro p hp f hf M hM hfJ w hw
  let F (z : (X dim)) := f z*c₀ (p,z)
  have hF : ContDiff ℝ ∞ F := hf.mul (hc₀.comp (contDiff_const.prodMk contDiff_id))
  let M' := (2:ℝ)^(dim+4)*(M*A)
  have hM' : 0 ≤ M' := by dsimp only [M']; positivity
  have hFJ (z : (X dim)) (hz : z ∈ S) (k : ℕ) (hk : k ≤ dim+4) : ‖iteratedFDeriv ℝ k F z‖ ≤ M' :=
    norm_iteratedFDeriv_mul_le_of_finite_bounds hf (hc₀.comp (contDiff_const.prodMk contDiff_id)) z hk
      hM (zero_le_one.trans hA) (hfJ z hz) (fun i hi =>
        (norm_iteratedFDeriv_slice_right_le hc₀ p z i).trans (hAjet (p,z) ⟨hp,hz⟩ i hi))
  let d (q : P × (X dim)) := F q.2
  have hdJ : ScaledSphereDatumJets (0+dim+4) d p 1 M' := by
    intro z hz
    refine ⟨d,hF.comp contDiff_snd,Filter.EventuallyEq.rfl,fun k hk => ?_⟩
    exact (norm_angular_iteratedFDeriv_of_frozen_parameter hF (0:P) z k).trans (hFJ z hz k (by simpa only [zero_add] using hk))
  have hDiff := (hDCon d p hp 1 M' one_ne_zero (by norm_num) hM' hdJ).2 w hw
  have hDiffB : ‖ballConormalDifference g d (p,w)‖ ≤ D*M' := by
    simpa only [norm_iteratedFDeriv_zero] using hDiff.1 0 le_rfl
  have hRaw : ‖radialBallConormal g (fun _ => F) (p,w)‖ ≤ B*M' := by
    rw [radialBallConormal,sphereNormalize_eq_of_sphere hw,ballConormal_eq_fderiv_conormalVector]
    have hFder : ‖fderiv ℝ F w‖ ≤ M' := (norm_iteratedFDeriv_one (𝕜 := ℝ) (x := w) F) ▸ hFJ w hw 1 (by omega)
    exact ((fderiv ℝ F w).le_opNorm _).trans
      ((mul_le_mul hFder (hBnd (p,w) ⟨hp,hw⟩) (norm_nonneg _) hM').trans_eq (mul_comm _ _))
  have hCn : ‖parametricBallConormal g d (p,w)‖ ≤ (D+B)*M' := by
    have he : parametricBallConormal g d (p,w) =
        ballConormalDifference g d (p,w)+radialBallConormal g (fun _ => F) (p,w) := by
      unfold ballConormalDifference
      exact (sub_add_cancel _ _).symm
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add hDiffB hRaw).trans_eq (by ring))
  let G := fun z => g (p,z)
  let U₀ := (Prod.mk p) ⁻¹' U
  have hU₀ : IsOpen U₀ := hU.preimage (continuous_const.prodMk continuous_id)
  have hBU₀ : closedBall (0 : (X dim)) 1 ⊆ U₀ := fun z hz => hJU ⟨hp,hz⟩
  have hg₀ : SmoothMetric U₀ G :=
    ⟨fun i j => (hg i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h),
      fun z hz => hPos _ hz⟩
  have hP := fixedBallPoisson_solution hU₀ hBU₀ hg₀
    (show smoothNear F S from ⟨univ,isOpen_univ,subset_univ _,hF.contDiffOn⟩)
  have hDEq : EqOn (fun z => velocityBoundaryDatum g V (fun q => f q.2) (p,z)) F S := by
    intro z hz
    change f z*c (p,z) = f z*c₀ (p,z)
    rw [hCeq (hJW₀ (show (p,z) ∈ J ×ˢ S from ⟨hp,hz⟩))]
  have hPEq := fixedBallPoisson_fderiv_eq_of_solution hU₀ hBU₀ hg₀ hP hDEq
  have hRotTerm (i j : (I dim)) :
      ‖sphereRotationDerivative i j (fun z => f z*t i j (p,z)) w‖ ≤ (2*T i j*max 0 (L i j))*M := by
    let Q (z : (X dim)) := f z*t₀ i j (p,z)
    have ht' : ContDiff ℝ ∞ (fun z => t₀ i j (p,z)) :=
      (ht₀ i j).comp (contDiff_const.prodMk contDiff_id)
    have hE : (fun z => f z*t i j (p,z)) =ᶠ[𝓝 w] Q := by
      have hMap : ContinuousAt (fun z => (p,z)) w :=
        ((continuous_const : Continuous (fun _ : (X dim) => p)).prodMk continuous_id).continuousAt
      filter_upwards [hMap.preimage_mem_nhds ((hW₁ i j).mem_nhds
        (hJW₁ i j (show (p,w) ∈ J ×ˢ S from ⟨hp,hw⟩)))] with z hz
      exact congrArg (f z * ·) (hTeq i j hz).symm
    have hQ : ‖fderiv ℝ Q w‖ ≤ 2*(M*T i j) := by
      rw [← norm_iteratedFDeriv_one]
      simpa only [pow_one] using norm_iteratedFDeriv_mul_le_of_finite_bounds hf ht' w (n := 1) (k := 1)
        le_rfl hM (zero_le_one.trans (hT₁ i j)) (fun k hk => hfJ w hw k (by omega)) (fun k hk =>
          (norm_iteratedFDeriv_slice_right_le (ht₀ i j) p w k).trans
            (hTjet i j (p,w) ⟨hp,hw⟩ k hk))
    rw [sphereRotationDerivative,hE.fderiv_eq]
    refine ((fderiv ℝ Q w).le_opNorm _).trans ?_
    exact (mul_le_mul hQ ((hL i j w hw).trans (le_max_right _ _)) (norm_nonneg _) (mul_nonneg (by norm_num) (mul_nonneg hM (zero_le_one.trans (hT₁ i j))))).trans_eq (by ring)
  rw [parametricBallVelocityAdjoint_on_sphere _ _ _ _ hw,ballVelocityAdjoint,
    ballConormal_eq_fderiv_conormalVector,hPEq (sphere_subset_closedBall hw)]
  have he : (fderiv ℝ (fixedBallPoisson G F) w) (ballConormalVector G w) =
      parametricBallConormal g d (p,w) := by
    rw [parametricBallConormal,sphereNormalize_eq_of_sphere hw,ballConormal_eq_fderiv_conormalVector]
  change ‖fderiv ℝ (fixedBallPoisson G F) w (ballConormalVector G w) -
    ∑ i, ∑ j, sphereRotationDerivative i j (fun z => f z*t i j (p,z)) w‖ ≤ C*M
  rw [he]
  calc
    _ ≤ ‖parametricBallConormal g d (p,w)‖ +
        ∑ i : (I dim), ∑ j : (I dim), ‖sphereRotationDerivative i j (fun z => f z*t i j (p,z)) w‖ :=
      (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))))
    _ ≤ (D+B)*M' + ∑ i : (I dim), ∑ j : (I dim), (2*T i j*max 0 (L i j))*M :=
      add_le_add hCn (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hRotTerm i j)))
    _ = _ := by dsimp only [C,M']; simp only [← Finset.sum_mul]; ring

end CalderonN
