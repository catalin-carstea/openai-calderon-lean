import Proof.PhysicalFirstCoordinateAdjointFamily
import Proof.PhysicalTruncatedCovariantDerivativeNormalForm
import Proof.UniformScalarPrincipalConnectionTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma balanced_real_adjoint_sub {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T C : E →L[ℝ] E) (J A : H →L[ℝ] E) (w : ℝ)
    (hT : T.adjoint=T) (hA : T.comp A=C.adjoint.comp J) :
    T.comp (A-w • J)=(C-w • T).adjoint.comp J := by
  rw [map_sub,map_smul,hT,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp,hA]

def PhysicalPrincipalData.firstCovariantCoordinateHalfL {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (b : I) (x : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  P.firstDerivativeCoordinateHalfL x b-scalarPrincipalConnectionWeight d b x •
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)

def PhysicalFirstCommutatorPacket.covariantCoordinateAdjointHigher
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε) (b : I) (x : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  W.coordinateAdjointHigher b x-scalarPrincipalConnectionWeight d b x •
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)

lemma PhysicalPrincipalData.firstCovariantCoordinate_coarse_half_compatible
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (hY : IsOpen Y) {x : X} (hx : x ∈ Y) (b : I) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateCoarseL b x)=
      (P.firstCovariantCoordinateHalfL b x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hh := P.firstDerivativeCoordinate_coarse_low_compatible hd hY hx b
  apply ContinuousLinearMap.ext
  intro u
  have hg := DFunLike.congr_fun hh u
  simp only [ContinuousLinearMap.comp_apply] at hg
  simp only [PhysicalPrincipalData.firstCovariantCoordinateCoarseL,
    PhysicalPrincipalData.firstCovariantCoordinateHalfL,ContinuousLinearMap.comp_apply,
    _root_.sub_apply,_root_.smul_apply,map_sub,map_smul,sphereSobolevInclusionL_trans_apply,hg]

lemma PhysicalFirstCommutatorPacket.covariantCoordinateAdjointHigher_balanced
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε) (b : I) {x : X} (hx : x ∈ Y) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (W.covariantCoordinateAdjointHigher b x)=
      (P.firstCovariantCoordinateHalfL b x).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hh := W.coordinateAdjointHigher_balanced b hx
  exact balanced_real_adjoint_sub (E:=SphereSobolev (1/2:ℝ)) (H:=SphereSobolev (3/2:ℝ))
    _ _ _ _ _ sphereSobolevHalfNegativeInclusion_adjoint hh

theorem uniform_first_covariant_coordinate_adjoint_higher {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ A : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        ∀ b : I,ContDiffOn ℝ ∞ (A b) Y ∧ ∀ y ∈ Y,
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A b y)=
            (P.firstCovariantCoordinateHalfL b y).adjoint.comp
              (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
          ‖A b y‖ ≤ C*ε/beta d.γ d.radius y := by
  obtain ⟨η,CB,CS,hη,hη1,hCB,hCS,hPacket⟩ := uniform_physical_first_commutator_packet
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  let C := 3*K*CB+CW
  have hK0 := zero_le_one.trans hK
  refine ⟨η,C,hη,hη1,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨W⟩ := hPacket floor hf ε hε hSmall d hd CT P
  let A := W.covariantCoordinateAdjointHigher
  refine ⟨A,?_⟩
  intro b
  have hw := hWeight floor hf ε hε (hSmall.trans hη1) d hd b
  refine ⟨(W.coordinateAdjointHigher_smooth hd b).sub (hw.1.smul contDiffOn_const),?_⟩
  intro y hy
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 := zero_le_one.trans hβ
  have hWN : ‖scalarPrincipalConnectionWeight d b y •
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)‖ ≤ CW*ε/beta d.γ d.radius y := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |scalarPrincipalConnectionWeight d b y| *1 :=
        mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le (3/2:ℝ) (1/2:ℝ) (by norm_num)) (abs_nonneg _)
      _ = |scalarPrincipalConnectionWeight d b y| := mul_one _
      _ ≤ CW*ε/(beta d.γ d.radius y)^2 := (hw.2 y hy (0:I) (0:I)).1
      _ ≤ CW*ε/beta d.γ d.radius y := by
        apply div_le_div_of_nonneg_left (mul_nonneg hCW hε) (zero_lt_one.trans_le hβ)
        nlinarith only [hβ]
  refine ⟨W.covariantCoordinateAdjointHigher_balanced b hy,?_⟩
  calc
    _ ≤ ‖W.coordinateAdjointHigher b y‖+‖scalarPrincipalConnectionWeight d b y •
        sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)‖ := norm_sub_le _ _
    _ ≤ (3*K*CB)*ε/beta d.γ d.radius y+CW*ε/beta d.γ d.radius y :=
      add_le_add (W.norm_coordinateAdjointHigher_le hd hK b hy) hWN
    _ = _ := by dsimp only [C];ring

end ShrinkingSpheres
