import Proof.FrameAdjointNormalForm
import Proof.ActualFirstAdjointErrorFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 25
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def actualFrameFirstAdjointErrorFamily (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i : I) (x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  ∑ a : I,d.frame x i a • actualFirstAdjointErrorFamily d (axis a) A (G a) x

lemma contDiffOn_actualFrameFirstAdjointErrorFamily {Y : Set X} (d : Data)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hE : ∀ a,ContDiffOn ℝ ∞ (actualFirstAdjointErrorFamily d (axis a) A (G a)) Y) (i : I) :
    ContDiffOn ℝ ∞ (actualFrameFirstAdjointErrorFamily d A G i) Y := by
  apply ContDiffOn.sum
  intro a _
  exact ((EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.comp_contDiffOn (he i)).smul (hE a)

lemma norm_actualFrameFirstAdjointErrorFamily_le {Y Ω : Set X} (hSub : Y ⊆ Ω)
    {m : ℕ} {K : ℝ} {M : Fin (m+1) → ℝ} (hK : 1 ≤ K) (d : Data)
    (hd : Background Ω K M d.γ d.g₁ d.g₂ d.frame)
    (A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (CE : ℝ) (hE : ∀ a,∀ x ∈ Y,‖actualFirstAdjointErrorFamily d (axis a) A (G a) x‖ ≤ CE*d.radius x)
    (i : I) {x : X} (hx : x ∈ Y) :
    ‖actualFrameFirstAdjointErrorFamily d A G i x‖ ≤ (3*K*CE)*d.radius x := by
  have hFrame := hd.2.2.2.2.2.2.2 x (hSub hx)
  exact (norm_weighted_sum_three_le (fun a => d.frame x i a)
    (fun a => actualFirstAdjointErrorFamily d (axis a) A (G a) x) K (CE*d.radius x)
    (zero_le_one.trans hK) (fun a => hd.1.frame_component_abs_le hK d.frame (hSub hx) hFrame i a)
    (fun a => hE a x hx)).trans_eq (by ring)
end ShrinkingSpheres
