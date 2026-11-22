module

public import Proof.CalderonN.UniformConormalCalculus

import Proof.Manuscript.TaylorModel
import Proof.Manuscript.MixedGreenJets
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

variable {P Q F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contDiff_parameterDerivative {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (v : P) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ (fun q => f (q,z)) p v) := by
  have h (z : Q) : fderiv ℝ (fun q => f (q,z)) p v = fderiv ℝ f (p,z) (v,0) := by
    change fderiv ℝ (f ∘ fun q => (q,z)) p v = _
    rw [(((hf.differentiable (by simp) (p,z)).hasFDerivAt).comp p
      (hasFDerivAt_prodMk_left p z)).fderiv]
    rfl
  simp only [h]
  exact ((hf.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const

private theorem iteratedFDeriv_parameterDerivative {f : P × Q → F} (hf : ContDiff ℝ ∞ f)
    (p : P) (v : P) (w : Q) (j : ℕ) :
    iteratedFDeriv ℝ j (fun z => fderiv ℝ (fun q => f (q,z)) p v) w =
      fderiv ℝ (fun q => iteratedFDeriv ℝ j (fun z => f (q,z)) w) p v := by
  let L := ContinuousLinearMap.apply ℝ F v
  have hD : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun q => f (q,z)) p) := by
    have h (z : Q) : fderiv ℝ (fun q => f (q,z)) p =
        (fderiv ℝ f (p,z)).comp (ContinuousLinearMap.inl ℝ P Q) := by
      exact (((hf.differentiable (by simp) (p,z)).hasFDerivAt).comp p
        (hasFDerivAt_prodMk_left p z)).fderiv
    simp only [h]
    exact ((hf.fderiv_right (m := ∞) (by simp)).comp
      (contDiff_const.prodMk contDiff_id)).clm_comp contDiff_const
  ext m
  change iteratedFDeriv ℝ j (L ∘ fun z => fderiv ℝ (fun q => f (q,z)) p) w m = _
  rw [L.iteratedFDeriv_comp_left hD.contDiffAt (by simp)]
  exact Probes.apply_iteratedFDeriv_fderiv_first_slice hf p w j m v

private theorem fderiv_spatialDerivative {b : P × Q → ℝ} (hb : ContDiff ℝ ∞ b)
    (p : P) (v : P) (w : Q) :
    fderiv ℝ (fun q => fderiv ℝ (fun z => b (q,z)) w) p v =
      fderiv ℝ (fun z => fderiv ℝ (fun q => b (q,z)) p v) w := by
  let L := (continuousMultilinearCurryFin1 ℝ Q ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let G (q : P) := iteratedFDeriv ℝ 1 (fun z => b (q,z)) w
  have hG : ContDiff ℝ ∞ G :=
    (contDiff_iteratedFDeriv_slice_right hb 1).comp (contDiff_id.prodMk contDiff_const)
  have hL : (fun q => fderiv ℝ (fun z => b (q,z)) w) = L ∘ G := by
    funext q
    ext u
    exact (iteratedFDeriv_one_apply (f := fun z => b (q,z)) (x := w) (fun _ => u)).symm
  rw [hL,(L.hasFDerivAt.comp p (hG.differentiable (by simp) p).hasFDerivAt).fderiv]
  change L (fderiv ℝ G p v) = _
  rw [← iteratedFDeriv_parameterDerivative hb p v w 1]
  ext u
  exact iteratedFDeriv_one_apply (f := fun z => fderiv ℝ (fun q => b (q,z)) p v)
    (x := w) (fun _ => u)

private theorem contDiff_spatialDerivative {b : P × Q → ℝ} (hb : ContDiff ℝ ∞ b)
    {N : Q → Q} (hN : ContDiff ℝ ∞ N) :
    ContDiff ℝ ∞ (fun q : P × Q => fderiv ℝ (fun z => b (q.1,z)) (N q.2)) := by
  have h (q : P × Q) : fderiv ℝ (fun z => b (q.1,z)) (N q.2) =
      (fderiv ℝ b (q.1,N q.2)).comp (ContinuousLinearMap.inr ℝ P Q) :=
    (((hb.differentiable (by simp) (q.1,N q.2)).hasFDerivAt).comp (N q.2)
      (hasFDerivAt_prodMk_right q.1 (N q.2))).fderiv
  simp only [h]
  exact ((hb.fderiv_right (m := ∞) (by simp)).comp
    (contDiff_fst.prodMk (hN.comp contDiff_snd))).clm_comp contDiff_const

private theorem norm_iteratedFDeriv_normalizedGradient_apply_le
    {b : Q → ℝ} {A N : Q → Q} (hb : ContDiff ℝ ∞ b) (hA : ContDiff ℝ ∞ A)
    (hN : ContDiff ℝ ∞ N) {w : Q} (hNw : N w = w) {n k : ℕ} (hk : k ≤ n)
    {M D T : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hT : 1 ≤ T)
    (hbJ : ∀ j ≤ n+1, ‖iteratedFDeriv ℝ j b w‖ ≤ M)
    (hAJ : ∀ j ≤ n, ‖iteratedFDeriv ℝ j A w‖ ≤ D)
    (hNJ : ∀ j ≤ n, ‖iteratedFDeriv ℝ j N w‖ ≤ T) :
    ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ b (N z) (A z)) w‖ ≤
      (2 : ℝ)^n * ((n.factorial : ℝ)*M*T^n*D) := by
  let B := fderiv ℝ b ∘ N
  have hF : ContDiff ℝ ∞ (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hBJ (j : ℕ) (hj : j ≤ n) :
      ‖iteratedFDeriv ℝ j B w‖ ≤ (n.factorial : ℝ)*M*T^n := by
    apply norm_iteratedFDeriv_comp_le_of_finite_bounds hF hN w hj hM hT
    · intro i hi
      rw [hNw,norm_iteratedFDeriv_fderiv]
      exact hbJ _ (by omega)
    · exact hNJ
  exact norm_iteratedFDeriv_clm_apply_le_of_finite_bounds (hF.comp hN) hA w hk
    (by positivity) hD hBJ hAJ

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 3600000 in
/-- A first parameter derivative of every angular conormal jet can be
estimated using only one parameter derivative of the spatial jets. -/
theorem exists_uniform_radialBallConormal_mixed_bounds
    (n : ℕ) {U : Set (P × X dim)} (hU : IsOpen U) {J : Set P} (hJ : IsCompact J)
    (hJU : J ×ˢ standardSphere dim ⊆ U)
    {g : P × X dim → Mat dim} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : P → X dim → ℝ) (p : P), p ∈ J →
      (∀ q, ContDiff ℝ ∞ (b q)) → ∀ w ∈ standardSphere dim,
      ∀ V : Set P, IsOpen V → p ∈ V →
      (∀ j ≤ n+1, ContDiffOn ℝ ∞ (fun q => iteratedFDeriv ℝ j (b q) w) V) →
      ∀ v : P, ∀ M L : ℝ, 0 ≤ M → 0 ≤ L →
      (∀ j ≤ n+1, ‖iteratedFDeriv ℝ j (b p) w‖ ≤ M) →
      (∀ j ≤ n+1, ‖fderiv ℝ (fun q => iteratedFDeriv ℝ j (b q) w) p v‖ ≤ L) →
      ∀ k ≤ n,
        ‖fderiv ℝ (fun q => iteratedFDeriv ℝ k
          (fun z => radialBallConormal g b (q,z)) w) p v‖ ≤ C*(L+M*‖v‖) := by
  let S := standardSphere dim
  have hS : IsCompact S := isCompact_sphere _ _
  let C₁ (q : P × X dim) := ballConormalVector (fun z => g (q.1,z)) q.2
  have hC₁ : ContDiffOn ℝ ∞ C₁ U := contDiffOn_product_ballConormalVector hg hPos
  obtain ⟨A,hA,_,O,hO,hJO,_,hEq⟩ :=
    exists_contDiff_extension_near_compact hU (hJ.prod hS) hJU hC₁
  let U₀ : Set (X dim) := {0}ᶜ
  have hSU : S ⊆ U₀ := by
    intro z hz hzero
    have hn := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z = 0 := mem_singleton_iff.mp hzero
    simp [hz0] at hn
  obtain ⟨N,hN,_,W,hW,hSW,_,hEqN⟩ := exists_contDiff_extension_near_compact
    (isClosed_singleton.isOpen_compl : IsOpen U₀) hS hSU contDiffOn_sphereNormalize
  let A' (q : P × X dim) := A (q.1,N q.2)
  have hA' : ContDiff ℝ ∞ A' := hA.comp (contDiff_fst.prodMk (hN.comp contDiff_snd))
  obtain ⟨D,hD,hDJ⟩ := exists_uniform_finite_jet_bound (hJ.prod hS) hA' (n+1)
  obtain ⟨T,hT,hTJ⟩ := exists_uniform_finite_jet_bound hS hN n
  let C := (2:ℝ)^n * (n.factorial : ℝ) * T^n * D
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro b p hp hb w hw V hV hpV hJets v M L hM hL hVJets hDJets k hk
  have hNw : N w = w := (hEqN (hSW hw)).trans (sphereNormalize_eq_of_sphere hw)
  obtain ⟨B,hB,hBJ⟩ := exists_smooth_spatial_jet_model hb hV hpV w (n+1) hJets
  let H (q : P × X dim) := fderiv ℝ (fun z => B (q.1,z)) (N q.2) (A' q)
  have hG : ContDiff ℝ ∞ (fun q : P × X dim => fderiv ℝ (fun z => B (q.1,z)) (N q.2)) :=
    contDiff_spatialDerivative hB hN
  have hH : ContDiff ℝ ∞ H := hG.clm_apply hA'
  have hAS (q : P) : ContDiff ℝ ∞ (fun z => A' (q,z)) :=
    hA'.comp (contDiff_const.prodMk contDiff_id)
  have hBJS (q : P) : ContDiff ℝ ∞ (fun z => B (q,z)) :=
    hB.comp (contDiff_const.prodMk contDiff_id)
  have hA0 (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i (fun z => A' (p,z)) w‖ ≤ D :=
    (norm_iteratedFDeriv_slice_right_le hA' p w i).trans (hDJ (p,w) ⟨hp,hw⟩ i (by omega))
  have hNV : ∀ i ≤ n, ‖iteratedFDeriv ℝ i N w‖ ≤ T := hTJ w hw
  have hMatch : (fun q => iteratedFDeriv ℝ k (fun z => radialBallConormal g b (q,z)) w) =ᶠ[𝓝 p]
      (fun q => iteratedFDeriv ℝ k (fun z => H (q,z)) w) := by
    have hpre : (fun q : P => (q,N w)) ⁻¹' O ∈ 𝓝 p :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (hO.mem_nhds (show (p,N w) ∈ O by rw [hNw]; exact hJO ⟨hp,hw⟩))
    filter_upwards [hpre,hBJ] with q hq hqJ
    let f (z : X dim) := fderiv ℝ (b q) (N z) (A' (q,z))
    have hf : ContDiff ℝ ∞ f :=
      (((hb q).fderiv_right (m := ∞) (by simp)).comp hN).clm_apply (hAS q)
    have hHp : ContDiff ℝ ∞ (fun z => H (q,z)) :=
      hH.comp (contDiff_const.prodMk contDiff_id)
    have he : (fun z => radialBallConormal g b (q,z)) =ᶠ[𝓝 w] f := by
      filter_upwards [hW.mem_nhds (hSW hw),
        (continuous_const.prodMk hN.continuous).continuousAt.preimage_mem_nhds (hO.mem_nhds hq)]
        with z hz hzO
      rw [radialBallConormal,ballConormal_eq_fderiv_conormalVector]
      change _ = fderiv ℝ (b q) (N z) (A (q,N z))
      have hzO' : (q,N z) ∈ O := hzO
      rw [hEq hzO',hEqN hz]
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
    have hZero : ∀ i ≤ n+1,
        ‖iteratedFDeriv ℝ i (b q - fun z => B (q,z)) w‖ ≤ 0 := by
      intro i hi
      rw [iteratedFDeriv_sub ((hb q).of_le (by simp)) ((hBJS q).of_le (by simp)),
        Pi.sub_apply,hqJ i hi,sub_self,norm_zero]
    -- The coefficient bound can be chosen separately at this nearby q.
    let Dq := ∑ i : Fin (n+1), ‖iteratedFDeriv ℝ i.val (fun z => A' (q,z)) w‖
    have hDq : 0 ≤ Dq := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hDqJ (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i (fun z => A' (q,z)) w‖ ≤ Dq := by
      let j : Fin (n+1) := ⟨i,by omega⟩
      change (fun j : Fin (n+1) => ‖iteratedFDeriv ℝ j.val (fun z => A' (q,z)) w‖) j ≤ Dq
      exact Finset.single_le_sum
        (f := fun j : Fin (n+1) => ‖iteratedFDeriv ℝ j.val (fun z => A' (q,z)) w‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have hdiff := norm_iteratedFDeriv_normalizedGradient_apply_le ((hb q).sub (hBJS q))
      (hAS q) hN hNw hk (le_rfl : (0:ℝ) ≤ 0) hDq hT hZero hDqJ hNV
    have hDiffFun : (fun z => fderiv ℝ (fun x => b q x - B (q,x)) (N z) (A' (q,z))) =
        f - fun z => H (q,z) := by
      funext z
      change fderiv ℝ (b q - fun x => B (q,x)) (N z) (A' (q,z)) = _
      rw [fderiv_sub ((hb q).differentiable (by simp) _)
        ((hBJS q).differentiable (by simp) _)]
      rfl
    rw [hDiffFun,iteratedFDeriv_sub (hf.of_le (by simp)) (hHp.of_le (by simp)),Pi.sub_apply] at hdiff
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hdiff) (norm_nonneg _)))
  rw [hMatch.fderiv_eq,← iteratedFDeriv_parameterDerivative hH p v w k]
  let D₁ (z : X dim) := fderiv ℝ (fun q => B (q,z)) p v
  let A₁ (z : X dim) := fderiv ℝ (fun q => A' (q,z)) p v
  have hD₁ : ContDiff ℝ ∞ D₁ := contDiff_parameterDerivative hB p v
  have hA₁ : ContDiff ℝ ∞ A₁ := contDiff_parameterDerivative hA' p v
  have hD₁J (i : ℕ) (hi : i ≤ n+1) : ‖iteratedFDeriv ℝ i D₁ w‖ ≤ L := by
    rw [iteratedFDeriv_parameterDerivative hB p v w i]
    have hBJ' : (fun q => iteratedFDeriv ℝ i (fun z => B (q,z)) w) =ᶠ[𝓝 p]
        (fun q => iteratedFDeriv ℝ i (b q) w) := hBJ.mono fun q hq => hq i hi
    rw [hBJ'.fderiv_eq]
    exact hDJets i hi
  have hBJ₀ (i : ℕ) (hi : i ≤ n+1) :
      ‖iteratedFDeriv ℝ i (fun z => B (p,z)) w‖ ≤ M :=
    ((mem_of_mem_nhds hBJ) i hi).symm ▸ hVJets i hi
  have hA₁J (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i A₁ w‖ ≤ D*‖v‖ := by
    rw [iteratedFDeriv_parameterDerivative hA' p v w i]
    exact (norm_fderiv_iteratedFDeriv_slice_right_le hA' p w i v).trans
      (mul_le_mul_of_nonneg_right (hDJ (p,w) ⟨hp,hw⟩ (i+1) (by omega)) (norm_nonneg _))
  have hRule : (fun z => fderiv ℝ (fun q => H (q,z)) p v) =
      (fun z => fderiv ℝ D₁ (N z) (A' (p,z)) + fderiv ℝ (fun x => B (p,x)) (N z) (A₁ z)) := by
    funext z
    have hslice : ContDiff ℝ ∞ (fun q : P => (q,z)) := contDiff_id.prodMk contDiff_const
    have hga : DifferentiableAt ℝ (fun q => fderiv ℝ (fun x => B (q,x)) (N z)) p :=
      (hG.comp hslice).differentiable (by simp) p
    have haa : DifferentiableAt ℝ (fun q => A' (q,z)) p :=
      (hA'.comp hslice).differentiable (by simp) p
    change fderiv ℝ (fun q => fderiv ℝ (fun x => B (q,x)) (N z) (A' (q,z))) p v = _
    rw [fderiv_clm_apply hga haa,add_comm]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    rw [fderiv_spatialDerivative hB p v (N z)]
  have hF₁ : ContDiff ℝ ∞ (fun z => fderiv ℝ D₁ (N z) (A' (p,z))) :=
    ((hD₁.fderiv_right (m := ∞) (by simp)).comp hN).clm_apply (hAS p)
  have hF₂ : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun x => B (p,x)) (N z) (A₁ z)) :=
    (((hBJS p).fderiv_right (m := ∞) (by simp)).comp hN).clm_apply hA₁
  rw [hRule]
  change ‖iteratedFDeriv ℝ k ((fun z => fderiv ℝ D₁ (N z) (A' (p,z))) +
    (fun z => fderiv ℝ (fun x => B (p,x)) (N z) (A₁ z))) w‖ ≤ _
  rw [iteratedFDeriv_add (hF₁.of_le (by simp)) (hF₂.of_le (by simp)),Pi.add_apply]
  calc
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ _ := add_le_add
      (norm_iteratedFDeriv_normalizedGradient_apply_le hD₁ (hAS p) hN hNw hk hL
        (zero_le_one.trans hD) hT hD₁J hA0 hNV)
      (norm_iteratedFDeriv_normalizedGradient_apply_le (hBJS p) hA₁ hN hNw hk hM
        (by positivity) hT hBJ₀ hA₁J hNV)
    _ = C*(L+M*‖v‖) := by dsimp [C]; ring

end CalderonPaper
