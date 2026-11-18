import Proof.ParallelScalarFirstHalfGerm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The same native coarse/half family supplies local smoothness of the
strong first half-jet and a genuine compatible second half-jet. The second
coarse witness is the actual ordered native derivative, not a smooth choice. -/
theorem strong_half_native_covariant_smooth_and_second
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K ρ c₀ floor ε : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (r0 : ℝ) {y : X} (hy : y ∈ Y) (b c : X)
    (H S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (F : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : NormalFrameRelativeParameter → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {D : Set NormalFrameRelativeParameter} (hD : IsOpen D)
    (hDsub : D ⊆ normalFrameRelativePositiveDomain Ω)
    (hp : normalFrameRelativeActualParameter d r0 y ∈ D)
    (hF : ContDiffOn ℝ ∞ F D) (hG : ContDiffOn ℝ ∞ G D)
    (hGerm : H =ᶠ[𝓝 y] fun x => F (normalFrameRelativeActualParameter d r0 x))
    (hS : ∀ x ∈ Y,CoarseCovariantRotationGraph d x b H (S x))
    (hL : ∀ x ∈ Y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S x)=
        (L x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hCompat : ∀ q ∈ D,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (F q)=
        (G q).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hGraph : ∀ q ∈ D,
      (∀ k l,metricPair d.γ q.1.1 (q.1.2 (axis k)) (q.1.2 (axis l))=if k=l then 1 else 0) →
      ∀ i j : I,∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (F q (sphereSobolevInclusionL 2 1 (by norm_num) u))=
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (normalFrameRelativeAngularDerivative d.γ F i j q
            (sphereSobolevInclusionL 2 1 (by norm_num) u)+F q (sphereSobolevRotationL 2 i j u))) :
    ContDiffAt ℝ ∞ L y ∧
    let p := normalFrameRelativeActualParameter d r0 y
    let B := normalFrameRelativeHorizontalField d.γ d.radius b
    let v := normalFrameRelativeHorizontalField d.γ d.radius c p
    let T := fderiv ℝ (fun q => fderiv ℝ F q (B q)) p v
    let N := fderiv ℝ (fun q => fderiv ℝ G q (B q)) p v
    CoarseCovariantRotationGraph d y c S T ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
        N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  let Q := normalFrameRelativeActualParameter d r0
  let B := normalFrameRelativeHorizontalField d.γ d.radius b
  have hQ : ContDiffAt ℝ ∞ Q y :=
    (contDiffOn_normalFrameRelativeActualParameter d r0 hd.2.2.2.2.1.1
      (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)
  have hB : ContDiffAt ℝ ∞ B (Q y) :=
    contDiffAt_relative_horizontal_field_of_admissible hY hΩ hSub hd hK _ hy b
  have hSGerm := coarse_covariant_native_horizontal_germ hY hΩ hSub hd hK
    r0 y hy b H S F D hD hp hF hGerm hS hGraph
  have hLGerm : L =ᶠ[𝓝 y] fun x => fderiv ℝ G (Q x) (B (Q x)) :=
    strong_half_native_horizontal_germ d r0 S L F G hD hF hG B hQ.continuousAt hp hSGerm
      (by filter_upwards [hY.mem_nhds hy] with x hx;exact hL x hx) hCompat
  have hGLocal := (((hG.contDiffAt (hD.mem_nhds hp)).fderiv_right (m:=∞) (by simp)).clm_apply hB).comp y hQ
  refine ⟨hGLocal.congr_of_eventuallyEq hLGerm,?_,?_⟩
  · exact coarse_second_covariant_graph_of_native_germ hY hΩ hSub hd hK
      r0 y hy b c H S F D hD hDsub hp hF hGerm hS hGraph
  · exact compatible_endpoint_second_horizontal F G _ _ hD hF hG B hp hB hCompat _

end ShrinkingSpheres.ParallelEnergy
