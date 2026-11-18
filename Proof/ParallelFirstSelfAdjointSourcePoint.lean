import Proof.ParallelFirstSelfAdjointSourceProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstSelfAdjointSourceJetError (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (b i : I) (y : X) : SphereSobolev (1/2:ℝ) :=
  firstSelfAdjointSourceDerivative P WF W U b i y-
    WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis i))

structure FirstSelfAdjointSourcePointBounds (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) (CA CL CJ : ℝ) : Prop where
  source : ∀ b,‖WF.covariantAdjointLowSection U b y‖ ≤
    CA*ε*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖
  weak : ∀ b i,‖weakHalfSourceCovariantDerivative d (WF.covariantAdjointLowSection U b) y (axis i)‖ ≤
    ε*(CL*‖halfSectionCovariantDerivativeL d
      (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (axis i)‖+
      CJ*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖)
  error : ∀ b i,‖firstSelfAdjointSourceJetError P WF W U b i y‖ ≤
    CJ*ε*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖

/-- Complete actual adjoint jets give strong coefficient errors but only
weak source derivatives. This is the orientation used in the energy pairing. -/
theorem first_self_adjoint_source_point_bounds
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    (hw : ∀ b,ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y)
    {y : X} (hy : y ∈ Y) {CA CL CJ : ℝ} (hCJ : 0 ≤ CJ) (hε : 0 ≤ ε)
    (hA : ∀ b,‖WF.covariantCoordinateAdjointHigher b y‖ ≤ CA*ε)
    (hL : ∀ b,‖P.firstCovariantCoordinateHalfL b y‖ ≤ CL*ε)
    (hJet : FirstSelfCompleteAdjointJetBound WF CJ) :
    FirstSelfAdjointSourcePointBounds P WF W U y CA CL CJ := by
  let V := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  refine ⟨?_,?_,?_⟩
  · intro b
    exact ((WF.covariantCoordinateAdjointHigher b y).le_opNorm (V y)).trans
      (mul_le_mul_of_nonneg_right (hA b) (norm_nonneg _))
  · intro b i
    obtain ⟨H,hH,hHN⟩ := hJet.jet b i y hy
    rw [first_self_adjoint_low_source_weak_product hY hΩ hd hK P WF U hU b i (hw b) hy,hH]
    have hHC : ‖(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H‖ ≤ CJ*ε :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (norm_sphereSobolevInclusionL_le _ _ _) hHN (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
    have hCN : ‖(P.firstCovariantCoordinateHalfL b y).adjoint‖ ≤ CL*ε := by
      simpa only [ContinuousLinearMap.adjoint.norm_map] using hL b
    let g := halfSectionCovariantDerivativeL d V y (axis i)
    have hGN : ‖(P.firstCovariantCoordinateHalfL b y).adjoint g‖ ≤ (CL*ε)*‖g‖ :=
      (((P.firstCovariantCoordinateHalfL b y).adjoint).le_opNorm g).trans
        (mul_le_mul_of_nonneg_right hCN (norm_nonneg g))
    have hVN : ‖((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H) (V y)‖ ≤
        (CJ*ε)*‖V y‖ :=
      (((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H).le_opNorm (V y)).trans
        (mul_le_mul_of_nonneg_right hHC (norm_nonneg _))
    have hN : ‖(P.firstCovariantCoordinateHalfL b y).adjoint g+
        ((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H) (V y)‖ ≤
        (CL*ε)*‖g‖+(CJ*ε)*‖V y‖ := (norm_add_le _ _).trans (add_le_add hGN hVN)
    exact hN.trans_eq (by dsimp only [V,g];ring)
  · intro b i
    obtain ⟨H,hH,hHN⟩ := hJet.jet b i y hy
    have hG := firstSelfAdjointSourceDerivative_eq_leading_add_jet hY hΩ hd hK P WF W U hU b i (hw b) hy H hH
    unfold firstSelfAdjointSourceJetError
    rw [hG,add_sub_cancel_left]
    exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_right hHN (norm_nonneg _))

end ShrinkingSpheres.ParallelEnergy
