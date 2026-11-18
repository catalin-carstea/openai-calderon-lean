import Proof.FourthBilinearVelocityBound
import Proof.CoordinateSprayThirdBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Local precomposition by a contraction does not increase any iterated
    derivative norm. This applies to the phase-space position projection. -/
lemma norm_iteratedFDeriv_comp_linear_le_of_norm_le_one
    {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set P} (hΩ : IsOpen Ω) (f : P → E) (hf : ContDiffOn ℝ ∞ f Ω)
    (L : Q →L[ℝ] P) (hL : ‖L‖ ≤ 1) (x : Q) (hx : L x ∈ Ω) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  have hPre := hΩ.preimage L.continuous
  have hEq := L.iteratedFDerivWithin_comp_right hf hΩ.uniqueDiffOn hPre.uniqueDiffOn hx (i:=n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hPre hx,iteratedFDerivWithin_of_isOpen n hΩ hx] at hEq
  rw [hEq]
  have hProd : (∏ _i : Fin n,‖L‖) ≤ 1 := by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg L) hL
  exact ((iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)).trans
    (mul_le_of_le_one_right (norm_nonneg _) hProd)

/-- The actual fourth geodesic-spray jet follows from the connection jets
    by two higher Leibniz estimates with the linear velocity projection. -/
theorem Elliptic.norm_fourth_coordinateGeodesicSpray_le {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (p : X × X) (hp : p.1 ∈ Ω) (V C2 C3 C4 : ℝ)
    (hV : 0 ≤ V) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hΓ2 : ‖iteratedFDeriv ℝ 2 (connectionBilinear g) p.1‖ ≤ C2)
    (hΓ3 : ‖iteratedFDeriv ℝ 3 (connectionBilinear g) p.1‖ ≤ C3)
    (hΓ4 : ‖iteratedFDeriv ℝ 4 (connectionBilinear g) p.1‖ ≤ C4)
    (hSpeed : ‖p.2‖ ≤ V) :
    ‖iteratedFDeriv ℝ 4 (coordinateGeodesicSpray g) p‖ ≤ C4*V^2+8*C3*V+12*C2 := by
  let π : (X × X) →L[ℝ] X := ContinuousLinearMap.fst ℝ X X
  let v : (X × X) →L[ℝ] X := ContinuousLinearMap.snd ℝ X X
  let U := π ⁻¹' Ω
  let A := connectionBilinear g ∘ π
  let B := fun q : X × X => A q (v q) (v q)
  have hU : IsOpen U := hΩ.preimage π.continuous
  have hpU : p ∈ U := hp
  have hπ : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.1‖ ≤ 1*‖q‖
    simpa only [one_mul] using norm_fst_le q
  have hv : ‖v‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.2‖ ≤ 1*‖q‖
    simpa only [one_mul] using norm_snd_le q
  have hΓ := hg.contDiffOn_connectionBilinear hΩ hK
  have hA : ContDiffOn ℝ ∞ A U := hΓ.comp_continuousLinearMap π
  have hA2 : ‖iteratedFDeriv ℝ 2 A p‖ ≤ C2 :=
    (norm_iteratedFDeriv_comp_linear_le_of_norm_le_one hΩ _ hΓ π hπ p hp 2).trans hΓ2
  have hA3 : ‖iteratedFDeriv ℝ 3 A p‖ ≤ C3 :=
    (norm_iteratedFDeriv_comp_linear_le_of_norm_le_one hΩ _ hΓ π hπ p hp 3).trans hΓ3
  have hA4 : ‖iteratedFDeriv ℝ 4 A p‖ ≤ C4 :=
    (norm_iteratedFDeriv_comp_linear_le_of_norm_le_one hΩ _ hΓ π hπ p hp 4).trans hΓ4
  have hB : ContDiffOn ℝ ∞ B U := (hA.clm_apply v.contDiff.contDiffOn).clm_apply v.contDiff.contDiffOn
  have hBAt := hB.contDiffAt (hU.mem_nhds hpU)
  have hBN : ‖iteratedFDeriv ℝ 4 B p‖ ≤ C4*V^2+8*C3*V+12*C2 :=
    norm_fourth_bilinear_linear_velocity_le hU A hA v hpU V C2 C3 C4 hV hC2 hC3 hC4 hv hSpeed hA2 hA3 hA4
  let iL : X →L[ℝ] X × X := ContinuousLinearMap.inl ℝ X X
  let iR : X →L[ℝ] X × X := ContinuousLinearMap.inr ℝ X X
  have hiR : ‖iR‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖((0,z):X × X)‖ ≤ 1*‖z‖
    simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg z),one_mul] using (le_refl ‖z‖)
  have hFun : coordinateGeodesicSpray g = fun q => iL (v q)-iR (B q) := by
    funext q
    change (q.2,-connection g q.1 q.2 q.2) = (q.2,0)-(0,connectionBilinear g q.1 q.2 q.2)
    rw [connectionBilinear_apply]
    simp
  have hLin : ‖iteratedFDeriv ℝ 4 (((iL.comp v) : (X × X) →L[ℝ] X × X) : (X × X) → X × X) p‖ = 0 :=
    norm_iteratedFDeriv_linear_higher (iL.comp v) p 2
  have hPost := iR.norm_iteratedFDeriv_comp_left hBAt (n:=4) (by simp)
  have hPostN : ‖iteratedFDeriv ℝ 4 (fun q => iR (B q)) p‖ ≤ ‖iteratedFDeriv ℝ 4 B p‖ :=
    hPost.trans ((mul_le_mul_of_nonneg_right hiR (norm_nonneg _)).trans_eq (one_mul _))
  rw [hFun]
  change ‖iteratedFDeriv ℝ 4 (((iL.comp v : (X × X) →L[ℝ] X × X) : (X × X) → X × X)-iR ∘ B) p‖ ≤ _
  have hL4 : ContDiffAt ℝ 4 (((iL.comp v) : (X × X) →L[ℝ] X × X) : (X × X) → X × X) p :=
    (iL.comp v).contDiff.contDiffAt
  have hRInfinity : ContDiffAt ℝ ∞ (iR ∘ B) p := iR.contDiff.contDiffAt.comp p hBAt
  have hR4 : ContDiffAt ℝ 4 (iR ∘ B) p := hRInfinity.of_le (by simp)
  rw [iteratedFDeriv_sub_apply hL4 hR4]
  exact (norm_sub_le _ _).trans (by rw [hLin,zero_add];exact hPostN.trans hBN)

end ShrinkingSpheres
