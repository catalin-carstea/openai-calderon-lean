import Proof.ParallelFirstSelfCorrectionNativeHalf
import Proof.PhysicalFirstCorrectionNativeCovariant
import Proof.PhysicalCorrectionStrongHalfData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The fixed actual bounded first jet, with its literal strong-half lift. -/
def correctionHalfCovariantFamily (d : Data) (b a x : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  halfLiftOfBoundedL2Operator (physicalFirstCorrectionBoundedCovariantJetL d x a b)

lemma correctionHalfCovariantFamily_coarse {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {x : X} (hx : x ∈ Y) (a b : X) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (physicalFirstCorrectionCovariantFamily d b x a)=
      (correctionHalfCovariantFamily d b a x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hSame := coarseCovariantRotationGraph_unique
    ((hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK b).2 x hx a)
    (hd.physicalFirstCorrection_covariant_graph hY hΩ hK hx a b)
  rw [hSame,←physicalFirstCorrectionBoundedCovariantJetL_coarse]
  exact halfLiftOfBoundedL2Operator_coarse _

private lemma correction_native_rotation_graph {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) (hp : p ∈ nativeFirstCorrectionDomain Y Ω)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0)
    (i j : I) (u : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (nativePhysicalFirstCorrectionFamily d r0 b p
        (sphereSobolevInclusionL 2 1 (by norm_num) u))=
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (normalFrameRelativeAngularDerivative d.γ (nativePhysicalFirstCorrectionFamily d r0 b) i j p
            (sphereSobolevInclusionL 2 1 (by norm_num) u)+
          nativePhysicalFirstCorrectionFamily d r0 b p (sphereSobolevRotationL 2 i j u)) := by
  have hpN : normalFrameRelativeNormalization d.γ p ∈ nativeFirstCorrectionDomain Y Ω :=
    ⟨hd.1.1.normalFrameRelativeNormalization_mem hK p hp.1,hp.2⟩
  have hF := hd.nativePhysicalFirstCorrectionFamily_smooth hY hΩ hK r0 b
  exact nativePhysicalFirstCorrection_normalized_rotation_graph hΩ d hd.1.1 hK r0 b p hp.1 he
    ((hF.contDiffAt ((isOpen_nativeFirstCorrectionDomain hY hΩ).mem_nhds hpN)).differentiableAt (by simp)) i j u

/-- A neighborhood identity for the SAME actual first half-jet. It is not
an independently selected family of pointwise extensions. -/
lemma correctionHalfCovariantFamily_native_germ {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (r0 : ℝ) (hr0 : r0 ≠ 0) {y : X} (hy : y ∈ Y) (a b : X) :
    correctionHalfCovariantFamily d b a =ᶠ[𝓝 y] fun x =>
      fderiv ℝ (correctionNativeHalfFamily d r0 b) (normalFrameRelativeActualParameter d r0 x)
        (normalFrameRelativeHorizontalField d.γ d.radius a (normalFrameRelativeActualParameter d r0 x)) := by
  let Q := normalFrameRelativeActualParameter d r0
  let F := nativePhysicalFirstCorrectionFamily d r0 b
  let G := correctionNativeHalfFamily d r0 b
  let B := normalFrameRelativeHorizontalField d.γ d.radius a
  let D := nativeFirstCorrectionDomain Y Ω
  have hD := isOpen_nativeFirstCorrectionDomain hY hΩ
  have hp := hd.1.nativeFirstCorrectionDomain_actual_parameter hSub r0 hy
  have hF := hd.nativePhysicalFirstCorrectionFamily_smooth hY hΩ hK r0 b
  have hG := correctionNativeHalfFamily_smooth hY hΩ hd hK r0 b
  have hQ : ContinuousAt Q y :=
    ((contDiffOn_normalFrameRelativeActualParameter d r0 hd.2.2.2.2.1.1
      (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)).continuousAt
  have hS := coarse_covariant_native_horizontal_germ hY hΩ hSub hd hK r0 y hy a
    (physicalFirstCorrectionCoarseFamily d b) (fun x => physicalFirstCorrectionCovariantFamily d b x a)
    F D hD hp hF
    (hd.nativePhysicalFirstCorrectionFamily_actual_germ hY hΩ hSub hK r0 hr0 hy b)
    (fun x hx => (hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK b).2 x hx a)
    (correction_native_rotation_graph hY hΩ hd hK r0 b)
  filter_upwards [hY.mem_nhds hy,hQ.eventually (hD.mem_nhds hp),hS] with x hx hxD hSx
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  have hL := correctionHalfCovariantFamily_coarse hY hΩ hSub hd hK hx a b
  rw [hSx] at hL
  apply hL.symm.trans
  apply compatible_endpoint_fderiv F G _ _ (Q x) (B (Q x))
    ((hF.contDiffAt (hD.mem_nhds hxD)).differentiableAt (by simp))
    ((hG.contDiffAt (hD.mem_nhds hxD)).differentiableAt (by simp))
  filter_upwards [hD.mem_nhds hxD] with p hpD
  exact correctionNativeHalfFamily_coarse d r0 b p

lemma correctionHalfCovariantFamily_smooth {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (a b : X) :
    ContDiffOn ℝ ∞ (correctionHalfCovariantFamily d b a) Y := by
  intro y hy
  let r0 := d.radius y
  let Q := normalFrameRelativeActualParameter d r0
  let G := correctionNativeHalfFamily d r0 b
  let B := normalFrameRelativeHorizontalField d.γ d.radius a
  have hD := isOpen_nativeFirstCorrectionDomain hY hΩ
  have hp := hd.1.nativeFirstCorrectionDomain_actual_parameter hSub r0 hy
  have hG := correctionNativeHalfFamily_smooth hY hΩ hd hK r0 b
  have hQ : ContDiffAt ℝ ∞ Q y :=
    (contDiffOn_normalFrameRelativeActualParameter d r0 hd.2.2.2.2.1.1
      (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)
  have hB : ContDiffAt ℝ ∞ B (Q y) :=
    contDiffAt_relative_horizontal_field_of_admissible hY hΩ hSub hd hK (Q y) hy a
  have hLocal := (((hG.contDiffAt (hD.mem_nhds hp)).fderiv_right (m:=∞) (by simp)).clm_apply hB).comp y hQ
  exact (hLocal.congr_of_eventuallyEq
    (correctionHalfCovariantFamily_native_germ hY hΩ hSub hd hK r0 (hd.2.2.2.2.1.2 y hy).1.ne' hy a b)).contDiffWithinAt

/-- Twice differentiating the literal native inclusion square gives the
second strong-half graph, aligned with the baseline actual coarse second jet. -/
lemma correctionHalfCovariantFamily_second_graph {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a c b : X) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let F := nativePhysicalFirstCorrectionFamily d (d.radius y) b
    let G := correctionNativeHalfFamily d (d.radius y) b
    let B := normalFrameRelativeHorizontalField d.γ d.radius a
    let v := normalFrameRelativeHorizontalField d.γ d.radius c p
    let T := fderiv ℝ (fun q => fderiv ℝ F q (B q)) p v
    let N := fderiv ℝ (fun q => fderiv ℝ G q (B q)) p v
    CoarseCovariantRotationGraph d y c (fun x => physicalFirstCorrectionCovariantFamily d b x a) T ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
        N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  dsimp only
  refine ⟨hd.physicalFirstCorrection_second_covariant_graph hY hΩ hSub hK hy a c b,?_⟩
  let F := nativePhysicalFirstCorrectionFamily d (d.radius y) b
  let G := correctionNativeHalfFamily d (d.radius y) b
  let B := normalFrameRelativeHorizontalField d.γ d.radius a
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hD := isOpen_nativeFirstCorrectionDomain hY hΩ
  have hp : p ∈ nativeFirstCorrectionDomain Y Ω := by
    simpa only [normalFrameRelativeActualParameter_point d y hr0] using
      hd.1.nativeFirstCorrectionDomain_actual_parameter hSub (d.radius y) hy
  have hF := hd.nativePhysicalFirstCorrectionFamily_smooth hY hΩ hK (d.radius y) b
  have hG := correctionNativeHalfFamily_smooth hY hΩ hd hK (d.radius y) b
  have hB : ContDiffAt ℝ ∞ B p := by
    simpa only [normalFrameRelativeActualParameter_point d y hr0] using
      contDiffAt_relative_horizontal_field_of_admissible hY hΩ hSub hd hK (normalFrameRelativeActualParameter d (d.radius y) y) hy a
  have hF' := ((hF.contDiffAt (hD.mem_nhds hp)).fderiv_right (m:=∞) (by simp)).clm_apply hB
  have hG' := ((hG.contDiffAt (hD.mem_nhds hp)).fderiv_right (m:=∞) (by simp)).clm_apply hB
  apply compatible_endpoint_fderiv _ _ _ _ p _
    (hF'.differentiableAt (by simp)) (hG'.differentiableAt (by simp))
  filter_upwards [hD.mem_nhds hp] with q hq
  apply compatible_endpoint_fderiv F G _ _ q (B q)
    ((hF.contDiffAt (hD.mem_nhds hq)).differentiableAt (by simp))
    ((hG.contDiffAt (hD.mem_nhds hq)).differentiableAt (by simp))
  exact Eventually.of_forall (fun r => correctionNativeHalfFamily_coarse d (d.radius y) b r)

end ShrinkingSpheres.ParallelEnergy
