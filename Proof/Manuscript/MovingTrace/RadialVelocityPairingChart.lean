module

public import Proof.Manuscript.MovingTrace.RadialVelocityOperator
public import Proof.Manuscript.AngularFourierResponse
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Proof.CalderonN.FixedBallPoissonCongruence

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
local notation "Z" => X dim
local notation "S" => standardSphere dim
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
namespace SmoothRadialVelocity

variable {G : BallPoissonTube P dim} (A : SmoothRadialVelocity G)

theorem operator_smoothNear {p : P} (hp : p ∈ A.U)
    {φ : Z → ℂ} (hφ : smoothNear φ S) : smoothNear (A.operator p φ) S := by
  obtain ⟨U,hU,hSU,hφU⟩ := hφ
  exact ⟨U ∩ A.S,hU.inter A.openS,subset_inter hSU A.sphere_mem,
    A.operator_contDiffOn hp (hU.inter A.openS) (subset_inter hSU A.sphere_mem)
      inter_subset_right (hφU.mono inter_subset_left)⟩

theorem operator_continuous_on_sphere {p : P} (hp : p ∈ A.U)
    {φ : Z → ℂ} (hφ : smoothNear φ S) :
    Continuous (fun z : ↥S => A.operator p φ z) := by
  obtain ⟨U,hU,hSU,hφU⟩ := A.operator_smoothNear hp hφ
  exact hφU.continuousOn.comp_continuous continuous_subtype_val (fun z => hSU z.property)

theorem integral_operator_pairing {p : P} (hp : p ∈ A.U)
    {φ g : Z → ℂ} (hφ : smoothNear φ S) (hg : smoothNear g S) :
    (∫ z : ↥S, A.operator p φ z * g z ∂sphereProbability dim) =
      ∫ z : ↥S, φ z * fderiv ℝ (complexFixedBallPoisson (fun x => G.g (p,x)) g)
        z (A.velocity (p,z)) ∂sphereProbability dim := by
  obtain ⟨U,hU,hSU,hφU⟩ := hφ
  obtain ⟨W,hW,hSW,hgW⟩ := hg
  let T := A.S ∩ (U ∩ W)
  have hT : IsOpen T := A.openS.inter (hU.inter hW)
  have hST : standardSphere dim ⊆ T := fun _ hz => ⟨A.sphere_mem hz,hSU hz,hSW hz⟩
  let O : Set Z := (Prod.mk p) ⁻¹' G.U
  have hO : IsOpen O := G.openU.preimage (continuous_const.prodMk continuous_id)
  have hTO : T ⊆ O := fun z hz => A.tube_mem ⟨hp,hz.1⟩
  have hV : ContDiffOn ℝ ∞ (fun z => A.velocity (p,z)) T := A.smoothV.comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz.1⟩)
  have hWeight : ContDiffOn ℝ ∞ (fun z => A.weight (p,z)) T := A.smoothW.comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => ⟨hp,hz.1⟩)
  exact integral_radialBallVelocityAdjoint_mul hO hT (A.closedBall_subset_metric_room hp) hST
    hTO (fun h => A.origin_off h.1) (A.metric_smooth_at_p hp)
    hV hWeight (fun z hz => A.weight_ne_zero (p,z) ⟨hp,hz.1⟩) A.scale_ne_zero (A.radial p hp)
    (hφU.mono (fun _ h => h.2.1)) (hgW.mono (fun _ h => h.2.2))

theorem operator_congr_on_sphere {p : P} (hp : p ∈ A.U)
    {φ ψ : Z → ℂ} (hφ : smoothNear φ S) (hψ : smoothNear ψ S)
    (hEq : EqOn φ ψ S) : EqOn (A.operator p φ) (A.operator p ψ) S := by
  have hC := (A.operator_continuous_on_sphere hp hφ).sub (A.operator_continuous_on_sphere hp hψ)
  have hZero : ∀ w : ↥S, A.operator p φ w - A.operator p ψ w = 0 := by
    apply eq_zero_of_sphere_smooth_test_pairings hC
    intro t ht
    have htS : smoothNear (fun z => (t z : ℂ)) S :=
      ⟨univ,isOpen_univ,subset_univ _,(Complex.ofRealCLM.contDiff.comp ht).contDiffOn⟩
    have hInt (f : Z → ℂ) (hf : smoothNear f S) :
        Integrable (fun z : ↥S => A.operator p f z * (t z : ℂ)) (sphereProbability dim) := by
      have : CompactSpace ↥S := isCompact_iff_compactSpace.mp (isCompact_sphere (0:Z) 1)
      exact ((A.operator_continuous_on_sphere hp hf).mul
        (Complex.continuous_ofReal.comp (ht.continuous.comp continuous_subtype_val))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    change (∫ z : ↥S, (A.operator p φ z - A.operator p ψ z) * (t z : ℂ) ∂sphereProbability dim) = 0
    simp only [sub_mul]
    rw [integral_sub (hInt φ hφ) (hInt ψ hψ),A.integral_operator_pairing hp hφ htS,
      A.integral_operator_pairing hp hψ htS,sub_eq_zero]
    apply integral_congr_ae
    filter_upwards with z
    rw [hEq z.property]
  exact fun z hz => sub_eq_zero.mp (hZero ⟨z,hz⟩)

theorem complexFixedBallPoisson_fderiv_congr {p : P} (hp : p ∈ A.U)
    {φ ψ : Z → ℂ} (hφ : smoothNear φ S) (hEq : EqOn ψ φ S) :
    EqOn (fderiv ℝ (complexFixedBallPoisson (fun z => G.g (p,z)) ψ))
      (fderiv ℝ (complexFixedBallPoisson (fun z => G.g (p,z)) φ)) (closedBall (0:Z) 1) := by
  obtain ⟨U,hU,hSU,hφU⟩ := hφ
  let g := fun z => G.g (p,z)
  let O : Set Z := (Prod.mk p) ⁻¹' G.U
  have hO : IsOpen O := G.openU.preimage (continuous_const.prodMk continuous_id)
  have hB := A.closedBall_subset_metric_room hp
  have hM := A.metric_smooth_at_p hp
  have hφR := fixedBallPoisson_solution hO hB hM
    ⟨U,hU,hSU,Complex.reCLM.contDiff.comp_contDiffOn hφU⟩
  have hφI := fixedBallPoisson_solution hO hB hM
    ⟨U,hU,hSU,Complex.imCLM.contDiff.comp_contDiffOn hφU⟩
  have heR : EqOn (fun z => (ψ z).re) (fun z => (φ z).re) S :=
    fun z hz => congrArg Complex.re (hEq hz)
  have heI : EqOn (fun z => (ψ z).im) (fun z => (φ z).im) S :=
    fun z hz => congrArg Complex.im (hEq hz)
  have hR := fixedBallPoisson_fderiv_eq_of_solution hO hB hM hφR heR
  have hI := fixedBallPoisson_fderiv_eq_of_solution hO hB hM hφI heI
  have hψR : FixedBallSolution g (fun z => (ψ z).re) (fixedBallPoisson g (fun z => (ψ z).re)) := by
    have hex : ∃ b, FixedBallSolution g (fun z => (ψ z).re) b :=
      ⟨_,⟨hφR.1,hφR.2.1.trans heR.symm,hφR.2.2⟩⟩
    unfold fixedBallPoisson
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  have hψI : FixedBallSolution g (fun z => (ψ z).im) (fixedBallPoisson g (fun z => (ψ z).im)) := by
    have hex : ∃ b, FixedBallSolution g (fun z => (ψ z).im) b :=
      ⟨_,⟨hφI.1,hφI.2.1.trans heI.symm,hφI.2.2⟩⟩
    unfold fixedBallPoisson
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  intro z hz
  ext v
  rw [fderiv_complexFixedBallPoisson_apply z v (hψR.1.differentiable (by simp) z)
    (hψI.1.differentiable (by simp) z),
    fderiv_complexFixedBallPoisson_apply z v (hφR.1.differentiable (by simp) z)
      (hφI.1.differentiable (by simp) z),hR hz,hI hz]
  rfl

end SmoothRadialVelocity
end CalderonPaper
