module

public import Proof.CalderonN.UniformMetricBallPoissonJets
public import Proof.CalderonN.UniformConormalCalculus
public import Proof.CalderonN.ScaledSphereDatumExtension

import Proof.CalderonN.FixedBallPoissonCongruence
import Mathlib.Tactic

/-! Adapted from `UniformBallConormalDifference` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 8500000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

@[expose] def ballConormalDifference (g : P × (X dim) → (Mat dim)) (d : P × (X dim) → ℝ) (q : P × (X dim)) : ℝ :=
  parametricBallConormal g d q-radialBallConormal g (fun p z => d (p,z)) q

private theorem contDiffOn_radialBallConormal_of_smooth_datum
    {W U : Set (P × (X dim))} {V : Set P} {g : P × (X dim) → (Mat dim)}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U) (hPos : ∀ q ∈ U, (g q).PosDef)
    {d : P × (X dim) → ℝ} (hd : ContDiff ℝ ∞ d)
    (hW : MapsTo (fun q : P × (X dim) => (q.1,sphereNormalize q.2)) W U)
    (hWV : W ⊆ V ×ˢ ({0}ᶜ : Set (X dim))) :
    ContDiffOn ℝ ∞ (radialBallConormal g (fun p z => d (p,z))) W := by
  let C (q : P × (X dim)) := ballConormalVector (fun z => g (q.1,z)) q.2
  have hC : ContDiffOn ℝ ∞ C U := contDiffOn_product_ballConormalVector hg hPos
  let D (q : P × (X dim)) := (q.1,sphereNormalize q.2)
  have hD : ContDiffOn ℝ ∞ D W :=
    contDiff_fst.contDiffOn.prodMk (contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn
      (fun q hq => (hWV hq).2))
  have hF : ContDiff ℝ ∞ (fun q : P × (X dim) => fderiv ℝ (fun z => d (q.1,z)) q.2) := by
    have he (q : P × (X dim)) :
        fderiv ℝ (fun z => d (q.1,z)) q.2 =
          (fderiv ℝ d q).comp (ContinuousLinearMap.inr ℝ P (X dim)) :=
      (((hd.differentiable (by simp) q).hasFDerivAt).comp q.2
        (hasFDerivAt_prodMk_right q.1 q.2)).fderiv
    simp only [he]
    exact (hd.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
  apply ((hF.contDiffOn.clm_apply hC).comp hD hW).congr
  intro q _
  exact ballConormal_eq_fderiv_conormalVector _ _ _

/-- The difference of harmonic and raw conormals inherits the required
angular jets and one radius-weighted parameter derivative. -/
theorem exists_uniform_ballConormalDifference_jets
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    {U : Set (P × (X dim))} (hU : IsOpen U) {J : Set P} (hJ : IsCompact J)
    (hJU : J ×ˢ closedBall (0 : (X dim)) 1 ⊆ U)
    {g : P × (X dim) → (Mat dim)} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : P × (X dim) → ℝ) (p : P), p ∈ J →
      ∀ r M : ℝ, r ≠ 0 → |r| ≤ R → 0 ≤ M →
      ScaledSphereDatumJets (n+dim+4) d p r M →
      (∃ V : Set P, IsOpen V ∧ p ∈ V ∧
        ContDiffOn ℝ ∞ (ballConormalDifference g d) (V ×ˢ ({0}ᶜ : Set (X dim)))) ∧
      ∀ w ∈ (standardSphere dim),
        (∀ k ≤ n, ‖iteratedFDeriv ℝ k (fun z => ballConormalDifference g d (p,z)) w‖ ≤ C*M) ∧
        ∀ v : P, ‖fderiv ℝ (fun q => ballConormalDifference g d (q,w)) p (r • v)‖ ≤ C*M*‖v‖ := by
  let s := n+1
  let S := (standardSphere dim)
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  let Cb := closedBall (0 : (X dim)) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hSN : S ⊆ N := by
    intro z hz
    change z ≠ 0
    intro h
    have := mem_sphere_zero_iff_norm.mp hz
    simp [h] at this
  have hJs : J ×ˢ S ⊆ U :=
    (Set.prod_mono (Subset.refl J) sphere_subset_closedBall).trans hJU
  obtain ⟨V₀,hV₀,hJV₀,B,hB,hPoisson⟩ := exists_uniform_metricBallPoisson_jet_bounds s hU hJ hJU hg hPos
  obtain ⟨L,hL,A,hA,hExtend⟩ := exists_scaledSphereDatum_extensions (dim := dim) (P := P) (s+dim+2)
  obtain ⟨D,hD,hCon⟩ := exists_uniform_radialBallConormal_bounds n hU hJ hJs hg hPos
  let C := D*(B*A+1)*(1+2*R)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro d p hp r M hr hrad hM hJets
  obtain ⟨d₀,d₁,hd₀,hd₁,hSupp,⟨U',hU',hSU',hdE⟩,hDE,hD₀,hD₁⟩ :=
    hExtend d p r M hr hM (by simpa only [s,show n+1+dim+2+1 = n+dim+4 by omega] using hJets)
  obtain ⟨b,hb,hSol,hMetric,hbDiff,hbBound⟩ := hPoisson d₁ hd₁ L hL hSupp
  obtain ⟨V₁,W,hV₁,hW,hpW,hSW,hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p)) hS (hU'.inter hU)
    (fun q hq => ⟨hSU' hq,hJs ⟨(mem_singleton_iff.mp hq.1).symm ▸ hp,hq.2⟩⟩)
  have hCUp : {p} ×ˢ Cb ⊆ U := fun q hq => hJU ⟨(mem_singleton_iff.mp hq.1).symm ▸ hp,hq.2⟩
  have hd : ContDiffOn ℝ ∞ d U' := hd₀.contDiffOn.congr (fun q hq => (hdE hq).symm)
  obtain ⟨V₂,hV₂,hp₂,hDCon⟩ := exists_contDiffOn_parametricBallConormal hU hU' p
    hCUp hSU' hg hPos hd
  let V := V₀ ∩ (V₁ ∩ V₂)
  have hV : IsOpen V := hV₀.inter (hV₁.inter hV₂)
  have hpV : p ∈ V := ⟨hJV₀ hp,hpW (mem_singleton _),hp₂⟩
  have hMap (q : P × (X dim)) (hq : q ∈ V ×ˢ N) : (q.1,sphereNormalize q.2) ∈ U' ∩ U :=
    hVW ⟨hq.1.2.1,hSW (sphereNormalize_mem_sphere hq.2)⟩
  have hEqRaw : EqOn (radialBallConormal g (fun p z => d (p,z)))
      (radialBallConormal g (fun p z => d₀ (p,z))) (V ×ˢ N) := by
    intro q hq
    let z := sphereNormalize q.2
    let F (z : (X dim)) := (q.1,z)
    have hEz : (fun x => d (q.1,x)) =ᶠ[𝓝 z] fun x => d₀ (q.1,x) := by
      filter_upwards [(continuous_const.prodMk continuous_id : Continuous F).continuousAt.preimage_mem_nhds
        (hU'.mem_nhds (hMap q hq).1)] with x hx
      exact (hdE hx).symm
    simp only [radialBallConormal,ballConormal_eq_fderiv_conormalVector]
    rw [hEz.fderiv_eq]
  have hEq : EqOn (ballConormalDifference g d)
      (radialBallConormal g (fun p => b p - fun z => d₀ (p,z))) (V ×ˢ N) := by
    intro q hq
    obtain ⟨U₀,hU₀,hBU₀,hgU₀⟩ := hMetric q.1 hq.1.1
    have hdB : EqOn (fun z => d (q.1,z)) (fun z => d₁ (q.1,z)) S := by
      intro z hz
      have hpz : (q.1,z) ∈ V₁ ×ˢ W := ⟨hq.1.2.1,hSW hz⟩
      have hs : (q.1,z) ∈ (univ : Set P) ×ˢ S := ⟨mem_univ _,hz⟩
      exact (hdE (hVW hpz).1).symm.trans (hDE hs).symm
    have hbEq := fixedBallPoisson_fderiv_eq_of_solution hU₀ hBU₀ hgU₀ (hSol q.1 hq.1.1) hdB
    let z := sphereNormalize q.2
    have hz : z ∈ Cb := sphere_subset_closedBall (sphereNormalize_mem_sphere hq.2)
    change parametricBallConormal g d q - radialBallConormal g (fun p z => d (p,z)) q = _
    rw [hEqRaw hq]
    simp only [parametricBallConormal,radialBallConormal,ballConormal_eq_fderiv_conormalVector]
    have hDiff : DifferentiableAt ℝ (fun x => d₀ (q.1,x)) z :=
      (hd₀.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) z
    rw [hbEq hz,fderiv_sub ((hb q.1).differentiable (by simp) z) hDiff]
    rfl
  have hSmooth : ContDiffOn ℝ ∞ (ballConormalDifference g d) (V ×ˢ N) := by
    have hRaw := contDiffOn_radialBallConormal_of_smooth_datum hg hPos hd₀
      (show MapsTo (fun q : P × (X dim) => (q.1,sphereNormalize q.2)) (V ×ˢ N) U from
        fun q hq => (hMap q hq).2) (Subset.refl _)
    have hRaw' := hRaw.congr (fun q hq => hEqRaw hq)
    exact (hDCon.mono (Set.prod_mono (fun q hq => hq.2.2) (Subset.refl _))).sub hRaw'
  refine ⟨⟨V,hV,hpV,hSmooth⟩,?_⟩
  intro w hw
  let b₀ (a : P) : (X dim) → ℝ := fun z => d₀ (a,z)
  let u (a : P) := b a-b₀ a
  have hb₀ (a : P) : ContDiff ℝ ∞ (b₀ a) := hd₀.comp (contDiff_const.prodMk contDiff_id)
  have hu : ContDiff ℝ ∞ (u p) := (hb p).sub (hb₀ p)
  have hSw : w ∈ Cb := sphere_subset_closedBall hw
  have hB₁ (v : P) : ∀ k ≤ s, ∀ z ∈ Cb,
      ‖iteratedFDeriv ℝ k (b p) z‖ ≤ B*(A*M) ∧
      ‖fderiv ℝ (fun q => iteratedFDeriv ℝ k (b q) z) p (r • v)‖ ≤
        B*((A*M)*‖v‖+(A*M)*‖r • v‖) :=
    hbBound p hp (r • v) (A*M) ((A*M)*‖v‖) (by positivity) (by positivity)
      (fun k hk z => (hD₁ k hk z (mem_univ _)).1)
      (fun k hk z => (hD₁ k hk z (mem_univ _)).2 v)
  have hUj (j : ℕ) (hj : j ≤ s) : ‖iteratedFDeriv ℝ j (u p) w‖ ≤ (B*A+1)*M := by
    rw [show u p = b p-b₀ p from rfl,iteratedFDeriv_sub ((hb p).of_le (by simp)) ((hb₀ p).of_le (by simp))]
    refine (norm_sub_le _ _).trans ?_
    exact (add_le_add (hB₁ 0 j hj w hSw).1 (hD₀ j (by omega) w hw).1).trans_eq (by ring)
  have hbD : DifferentiableAt ℝ (fun q => iteratedFDeriv ℝ 1 (b q) w) p :=
    ((hbDiff 1 (by omega) w hSw).contDiffAt (hV₀.mem_nhds (hJV₀ hp))).differentiableAt (by simp)
  have hb₀D : DifferentiableAt ℝ (fun q => iteratedFDeriv ℝ 1 (b₀ q) w) p :=
    ((contDiff_iteratedFDeriv_slice_right hd₀ 1).comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p
  have hEu : (fun q => iteratedFDeriv ℝ 1 (u q) w) =
      (fun q => iteratedFDeriv ℝ 1 (b q) w) - (fun q => iteratedFDeriv ℝ 1 (b₀ q) w) := by
    funext q
    change iteratedFDeriv ℝ 1 (b q-b₀ q) w = _
    rw [iteratedFDeriv_sub ((hb q).of_le (by simp)) ((hb₀ q).of_le (by simp))]
    rfl
  obtain ⟨hJ₁,hJ₂⟩ := hCon u p hp hu w hw
  constructor
  · intro k hk
    have hEqw : (fun z => ballConormalDifference g d (p,z)) =ᶠ[𝓝 w]
        (fun z => radialBallConormal g u (p,z)) := by
      filter_upwards [(isClosed_singleton.isOpen_compl : IsOpen N).mem_nhds (hSN hw)] with z hz
      exact hEq ⟨hpV,hz⟩
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hEqw k).eq_of_nhds]
    refine (hJ₁ ((B*A+1)*M) (by positivity) hUj k hk).trans ?_
    rw [show D*((B*A+1)*M) = (D*(B*A+1))*M by ring]
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (by positivity) (by linarith)) hM
  · intro v
    have he : (fun q => ballConormalDifference g d (q,w)) =ᶠ[𝓝 p]
        (fun q => radialBallConormal g u (q,w)) := by
      filter_upwards [hV.mem_nhds hpV] with q hq using hEq ⟨hq,hSN hw⟩
    rw [he.fderiv_eq]
    refine (hJ₂ (hEu ▸ hbD.sub hb₀D) (r • v)).trans ?_
    have hR' : ‖r • v‖ ≤ R*‖v‖ := by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hrad (norm_nonneg _)
    have hUD : ‖fderiv ℝ (fun q => iteratedFDeriv ℝ 1 (u q) w) p (r • v)‖ ≤
        ((B*A)*(1+R)+1)*M*‖v‖ := by
      rw [hEu,fderiv_sub hbD hb₀D]
      refine (norm_sub_le _ _).trans ?_
      calc
        _ ≤ B*(A*M*‖v‖+A*M*‖r • v‖)+M*‖v‖ :=
          add_le_add (hB₁ v 1 (by omega) w hSw).2 ((hD₀ 1 (by omega) w hw).2 v)
        _ ≤ B*(A*M*‖v‖+A*M*(R*‖v‖))+M*‖v‖ := by gcongr
        _ = _ := by ring
    calc
      _ ≤ D*(((B*A)*(1+R)+1)*M*‖v‖+((B*A+1)*M)*(R*‖v‖)) := by
        gcongr
        exact hUj 1 (by omega)
      _ ≤ C*M*‖v‖ := by
        have hT : 0 ≤ D*M*‖v‖*R := by positivity
        dsimp only [C]
        nlinarith

end CalderonN
