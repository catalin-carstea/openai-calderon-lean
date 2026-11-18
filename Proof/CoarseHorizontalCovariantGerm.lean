import Proof.FixedRelativeChartCovariantDerivative
import Proof.HorizontalDerivativeRotationGraph
import Proof.CoarseCovariantJetFamily
import Proof.ActualSmoothRadialTaylorPair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma contDiffAt_relative_horizontal_field_of_admissible
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K ρ c₀ floor ε : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (p : NormalFrameRelativeParameter) (hp : p.1.1 ∈ Y) (b : X) :
    ContDiffAt ℝ ∞ (normalFrameRelativeHorizontalField d.γ d.radius b) p := by
  have hG : ContDiffAt ℝ ∞ (connectionBilinear d.γ) p.1.1 :=
    (hd.1.1.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds (hSub hp))
  have hLog : ContDiffAt ℝ ∞ (fderiv ℝ (fun x => Real.log (d.radius x))) p.1.1 :=
    (((hd.2.2.2.2.1.1).log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')).contDiffAt
      (hY.mem_nhds hp)).fderiv_right (m:=∞) (by simp)
  have hG' : ContDiffAt ℝ ∞ (fun q : NormalFrameRelativeParameter => connectionBilinear d.γ q.1.1) p :=
    ContDiffAt.comp (f:=fun q : NormalFrameRelativeParameter => q.1.1)
      (g:=connectionBilinear d.γ) p hG contDiffAt_fst.fst
  have hLog' : ContDiffAt ℝ ∞ (fun q : NormalFrameRelativeParameter =>
      fderiv ℝ (fun x => Real.log (d.radius x)) q.1.1) p :=
    ContDiffAt.comp (f:=fun q : NormalFrameRelativeParameter => q.1.1)
      (g:=fderiv ℝ (fun x => Real.log (d.radius x))) p hLog contDiffAt_fst.fst
  exact contDiffAt_relativeHorizontalFieldOfFamilies _ _ b p hG' hLog'

/-- Uniqueness identifies any genuine first covariant derivative with the
horizontal derivative of the SAME native family in a neighborhood, not
just at the initially selected center. -/
theorem coarse_covariant_native_horizontal_germ
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K ρ c₀ floor ε : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (r0 : ℝ) (y : X) (hy : y ∈ Y) (b : X)
    (H S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (F : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (D : Set NormalFrameRelativeParameter) (hD : IsOpen D)
    (hp : normalFrameRelativeActualParameter d r0 y ∈ D)
    (hF : ContDiffOn ℝ ∞ F D)
    (hGerm : H =ᶠ[𝓝 y] fun x => F (normalFrameRelativeActualParameter d r0 x))
    (hS : ∀ x ∈ Y,CoarseCovariantRotationGraph d x b H (S x))
    (hGraph : ∀ q ∈ D,
      (∀ k l,metricPair d.γ q.1.1 (q.1.2 (axis k)) (q.1.2 (axis l)) =
        if k=l then 1 else 0) → ∀ i j : I,∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (F q (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (normalFrameRelativeAngularDerivative d.γ F i j q
            (sphereSobolevInclusionL 2 1 (by norm_num) u)+F q (sphereSobolevRotationL 2 i j u))) :
    S =ᶠ[𝓝 y] fun x => fderiv ℝ F (normalFrameRelativeActualParameter d r0 x)
      (normalFrameRelativeHorizontalField d.γ d.radius b (normalFrameRelativeActualParameter d r0 x)) := by
  have heS := hd.1.2.2.2.2.2.2.1
  have heF := hd.1.2.2.2.2.2.2.2
  have hQ := (contDiffOn_normalFrameRelativeActualParameter d r0 hd.2.2.2.2.1.1
    (fun i => (heS i).mono hSub)).contDiffAt (hY.mem_nhds hy)
  have hNearD : ∀ᶠ x in 𝓝 y,normalFrameRelativeActualParameter d r0 x ∈ D :=
    hQ.continuousAt.eventually (hD.mem_nhds hp)
  filter_upwards [hY.mem_nhds hy,hNearD,hGerm.eventuallyEq_nhds] with x hx hxD hxG
  have hE (i : I) := (heS i).contDiffAt (hΩ.mem_nhds (hSub hx))
  have hL := (contDiffAt_frameVectorLinear d.frame x hE).differentiableAt (by simp)
  have hFrame (i j : I) : metricPair d.γ x
      (frameVectorLinear d.frame x (axis i)) (frameVectorLinear d.frame x (axis j)) =
      if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using heF x (hSub hx) i j
  have hNative := fixed_relative_covariant_rotation_graph_of_germ d r0 x b H F hxG
    ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
    (hd.2.2.2.2.1.2 x hx).1.ne' hL (fun i => (hE i).differentiableAt (by simp))
    (heF x (hSub hx)) (frameConnection_skew hΩ hd.1.1 hK d.frame heS heF (hSub hx) b)
    ((hF.contDiffAt (hD.mem_nhds hxD)).differentiableAt (by simp))
    (hGraph _ hxD hFrame)
  exact coarseCovariantRotationGraph_unique (hS x hx) hNative

/-- A second covariant graph comes from two ordered horizontal derivatives
of the original native family. All endpoint equalities are genuine graphs. -/
theorem coarse_second_covariant_graph_of_native_germ
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K ρ c₀ floor ε : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (r0 : ℝ) (y : X) (hy : y ∈ Y) (b c : X)
    (H S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (F : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (D : Set NormalFrameRelativeParameter) (hD : IsOpen D)
    (hDsub : D ⊆ normalFrameRelativePositiveDomain Ω)
    (hp : normalFrameRelativeActualParameter d r0 y ∈ D)
    (hF : ContDiffOn ℝ ∞ F D)
    (hGerm : H =ᶠ[𝓝 y] fun x => F (normalFrameRelativeActualParameter d r0 x))
    (hS : ∀ x ∈ Y,CoarseCovariantRotationGraph d x b H (S x))
    (hGraph : ∀ q ∈ D,
      (∀ k l,metricPair d.γ q.1.1 (q.1.2 (axis k)) (q.1.2 (axis l)) =
        if k=l then 1 else 0) → ∀ i j : I,∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (F q (sphereSobolevInclusionL 2 1 (by norm_num) u)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (normalFrameRelativeAngularDerivative d.γ F i j q
            (sphereSobolevInclusionL 2 1 (by norm_num) u)+F q (sphereSobolevRotationL 2 i j u))) :
    CoarseCovariantRotationGraph d y c S
      (fderiv ℝ (fun q => fderiv ℝ F q (normalFrameRelativeHorizontalField d.γ d.radius b q))
        (normalFrameRelativeActualParameter d r0 y)
        (normalFrameRelativeHorizontalField d.γ d.radius c (normalFrameRelativeActualParameter d r0 y))) := by
  have heS := hd.1.2.2.2.2.2.2.1
  have heF := hd.1.2.2.2.2.2.2.2
  have hE (i : I) := (heS i).contDiffAt (hΩ.mem_nhds (hSub hy))
  have hL := (contDiffAt_frameVectorLinear d.frame y hE).differentiableAt (by simp)
  have hFrame (i j : I) : metricPair d.γ y
      (frameVectorLinear d.frame y (axis i)) (frameVectorLinear d.frame y (axis j)) =
      if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using heF y (hSub hy) i j
  have hFp := hF.contDiffAt (hD.mem_nhds hp)
  have hX := contDiffAt_relative_horizontal_field_of_admissible hY hΩ hSub hd hK
    (normalFrameRelativeActualParameter d r0 y) hy b
  have hFs : DifferentiableAt ℝ (fun q => fderiv ℝ F q
      (normalFrameRelativeHorizontalField d.γ d.radius b q))
      (normalFrameRelativeActualParameter d r0 y) :=
    ((hFp.fderiv_right (m:=∞) (by simp)).clm_apply hX).differentiableAt (by simp)
  apply fixed_relative_covariant_rotation_graph_of_germ d r0 y c S _
    (coarse_covariant_native_horizontal_germ hY hΩ hSub hd hK r0 y hy b H S F D hD hp hF hGerm hS hGraph)
    ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (hd.2.2.2.2.1.2 y hy).1.ne' hL (fun i => (hE i).differentiableAt (by simp))
    (heF y (hSub hy)) (frameConnection_skew hΩ hd.1.1 hK d.frame heS heF (hSub hy) c) hFs
  intro i j u
  exact horizontal_derivative_normalized_rotation_graph hΩ hd.1.1 hK d.radius hD hDsub _ hp hFrame b F hFp
    (hX.differentiableAt (by simp)) i j (fun q hq hqe => hGraph q hq hqe i j) u

end ShrinkingSpheres
