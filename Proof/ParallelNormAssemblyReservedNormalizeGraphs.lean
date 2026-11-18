import Proof.ParallelNormAssemblyReservedRadiusJets
import Proof.StrongHalfCovariantCalculus
import Proof.CovariantRotationGraphOperations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

def normalizedCoarseFirstJet (w : X → ℝ)
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (S : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (i : I) (x : X) :=
  w x • S i x+coordDeriv i w x • F x

def normalizedHalfFirstJet (w : X → ℝ)
    (F : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (S : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (i : I) (x : X) :=
  w x • S i x+coordDeriv i w x • F x

/-- Exact scalar normalization of a retained smooth coarse first jet and
its genuine coarse/half second graph. No higher endpoint is inferred. -/
lemma radius_normalized_coarse_half_two_jet_graph {Y : Set X} (hY : IsOpen Y)
    (d : Data) (w : X → ℝ) (hw : ContDiffOn ℝ ∞ w Y)
    (F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (FL : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (FH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (S : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hFS : ContDiffOn ℝ ∞ F Y) (hLS : ContDiffOn ℝ ∞ FL Y)
    (hSS : ∀ i,ContDiffOn ℝ ∞ (S i) Y) (hSL : ∀ i,ContDiffOn ℝ ∞ (L i) Y)
    (hBase : ∀ x ∈ Y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (F x)=
      (FL x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hGraph : ∀ i x, x ∈ Y → CoarseCovariantRotationGraph d x (axis i) F (S i x))
    (hCompat : ∀ i x,x ∈ Y → (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S i x)=
      (L i x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hStrong : ∀ i x,x ∈ Y → halfOperatorCovariantDerivativeL d FL FH x (axis i)=
      (L i x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (∀ i,ContDiffOn ℝ ∞ (normalizedCoarseFirstJet w F S i) Y ∧
      ContDiffOn ℝ ∞ (normalizedHalfFirstJet w FL L i) Y) ∧
    ∀ y ∈ Y,∀ i : I,
      CoarseCovariantRotationGraph d y (axis i) (fun x => w x • F x)
        (normalizedCoarseFirstJet w F S i y) ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (normalizedCoarseFirstJet w F S i y)=
        (normalizedHalfFirstJet w FL L i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      halfOperatorCovariantDerivativeL d (fun x => w x • FL x) (fun x => w x • FH x) y (axis i)=
        (normalizedHalfFirstJet w FL L i y).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ∀ j : I,∀ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∀ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      CoarseCovariantRotationGraph d y (axis j) (S i) T →
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
        N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) →
      let TN := (w y • T+coordDeriv j w y • S i y)+
        (coordDeriv i w y • S j y+coordDeriv j (coordDeriv i w) y • F y)
      let NN := (w y • N+coordDeriv j w y • L i y)+
        (coordDeriv i w y • L j y+coordDeriv j (coordDeriv i w) y • FL y)
      CoarseCovariantRotationGraph d y (axis j) (normalizedCoarseFirstJet w F S i) TN ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp TN=
        NN.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hwi (i : I) := contDiffOn_coordDeriv hY hw i
  have hDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : X → E}
      (hG : ContDiffOn ℝ ∞ G Y) {y : X} (hy : y ∈ Y) : DifferentiableAt ℝ G y :=
    (hG.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  refine ⟨fun i => ⟨(hw.smul (hSS i)).add ((hwi i).smul hFS),
    (hw.smul (hSL i)).add ((hwi i).smul hLS)⟩,?_⟩
  intro y hy i
  refine ⟨(hGraph i y hy).smul w (hDiff hw hy) (hDiff hFS hy),?_,?_,?_⟩
  · apply ContinuousLinearMap.ext
    intro u
    have h0 := DFunLike.congr_fun (hBase y hy) u
    have h1 := DFunLike.congr_fun (hCompat i y hy) u
    simp only [ContinuousLinearMap.comp_apply] at h0 h1
    simp only [normalizedCoarseFirstJet,normalizedHalfFirstJet,ContinuousLinearMap.comp_apply,
      _root_.add_apply,_root_.smul_apply,map_add,map_smul,h0,h1]
  · have hh := half_covariant_strong_smul d w FL FH y (axis i) (hw.contDiffAt (hY.mem_nhds hy))
      (hLS.contDiffAt (hY.mem_nhds hy)) (L i y) (hStrong i y hy)
    simpa only [normalizedHalfFirstJet,directionalFDeriv,coordDeriv,add_comm] using hh
  · intro j T N hT hN
    dsimp only
    have hG := (hT.smul w (hDiff hw hy) (hDiff (hSS i) hy)).add
      ((hGraph j y hy).smul (coordDeriv i w) (hDiff (hwi i) hy) (hDiff hFS hy))
      (hDiff (hw.smul (hSS i)) hy) (hDiff ((hwi i).smul hFS) hy)
    refine ⟨hG,?_⟩
    apply ContinuousLinearMap.ext
    intro u
    have h0 := DFunLike.congr_fun (hBase y hy) u
    have h1 := DFunLike.congr_fun (hCompat i y hy) u
    have h2 := DFunLike.congr_fun (hCompat j y hy) u
    have h3 := DFunLike.congr_fun hN u
    simp only [ContinuousLinearMap.comp_apply] at h0 h1 h2 h3
    simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.smul_apply,map_add,map_smul,h0,h1,h2,h3]

end ShrinkingSpheres.ParallelEnergy
