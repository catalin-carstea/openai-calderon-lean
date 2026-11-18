import Proof.UniformEffectiveFirstAngularCommutator
import Proof.EffectiveFirstCovariantCoarseBridge
import Proof.UniformPhysicalFirstCovariantCoordinateTwoJets
import Proof.CanonicalCoarseTripleEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def PhysicalFirstCommutatorPacket.covariantCoordinateAdjointDerivative
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε) (b i : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  halfOperatorCovariantDerivativeL d (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint)
    (W.covariantCoordinateAdjointHigher b) y (axis i)

def EffectiveFirstAdjointDerivativePairBound {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
    {P : PhysicalPrincipalData Y d CF CT} (W : PhysicalFirstCommutatorPacket P CB CS ε) (CE : ℝ) : Prop :=
  ∀ y ∈ Y,∀ b i : I,∀ u v : SphereSobolev (3/2:ℝ),
    |sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      (W.covariantCoordinateAdjointDerivative b i y v)| ≤
      CE*ε*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖*‖u‖

/-- True weak transpose bounds for derivatives of the SAME effective first
coefficient follow from its actual controlled covariant coarse jet. -/
theorem uniform_effective_first_adjoint_derivative_pair_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CB CS CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CB ∧ 0 ≤ CS ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ W : PhysicalFirstCommutatorPacket P CB CS ε,EffectiveFirstAdjointDerivativePairBound W CE := by
  have hPacketProduce := uniform_effective_first_angular_commutator hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  obtain ⟨ηW,CB,CS,hηW,hηW1,hCB,hCS,hPacket⟩ := hPacketProduce
  have hJetProduce := uniform_physical_first_covariant_coordinate_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηS,CE,hηS,hηS1,hCE,hJets⟩ := hJetProduce
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets hY hΩ (by omega) K ρ c₀ M Cj hK
  refine ⟨min ηW ηS,CB,CS,CE,lt_min hηW hηS,(min_le_left _ _).trans hηW1,hCB,hCS,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CT P
  obtain ⟨W,hGraphs⟩ := hPacket floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CT P
  obtain ⟨S,hS⟩ := hJets floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  have hWS (b : I) := (hWeight floor hf ε hε
    ((hSmall.trans (min_le_left _ _)).trans hηW1) d hd b).1
  refine ⟨W,?_⟩
  intro y hy b i u v
  let H := P.firstCovariantCoordinateHigherL b
  let A := W.covariantCoordinateAdjointHigher b
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let D := halfOperatorCovariantDerivativeL d (P.firstCovariantCoordinateHalfL b) H y (axis i)
  have hC := P.firstCovariantCoordinateHalfL_smooth hd hY hΩ (zero_lt_one.trans_le hK) b (hWS b)
  have hForward := (hGraphs y hy b b).1
  have hPair := half_covariant_adjoint_pairing d (P.firstCovariantCoordinateHalfL b) H A
    (hC.contDiffAt (hY.mem_nhds hy)) (axis i) hForward (W.covariantCoordinateAdjointHigher_balanced b hy) u v
  have hRows := (hS b i).2.2 y hy
  have hD := P.firstCovariantCoordinate_covariant_eq_coarse hd hY hΩ (zero_lt_one.trans_le hK) b
    (hWS b) (hS b i).1 hy (axis i) H hForward (S b i y) hRows.1
  have hDN : ‖D u‖ ≤ (CE*ε)*‖u‖ := by
    have hg := DFunLike.congr_fun hD u
    simp only [ContinuousLinearMap.comp_apply] at hg
    rw [show D u=sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (S b i y (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)) from hg]
    calc
      _ ≤ ‖S b i y (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)‖ :=
        norm_sphereSobolevInclusionL_apply_le 0 (-(1/2:ℝ)) (by norm_num) _
      _ ≤ ‖S b i y‖*‖sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u‖ := (S b i y).le_opNorm _
      _ ≤ (CE*ε)*‖u‖ := mul_le_mul hRows.2.2.1
        (norm_sphereSobolevInclusionL_apply_le (3/2:ℝ) 1 (by norm_num) u) (norm_nonneg _) (mul_nonneg hCE hε)
  change |sphereSobolevDualPairing (1/2:ℝ) (J u)
    (halfOperatorCovariantDerivativeL d (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint) A y (axis i) v)| ≤ _
  rw [hPair]
  change |⟪J v,D u⟫_ℝ| ≤ _
  calc
    _ ≤ ‖J v‖*‖D u‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖J v‖*((CE*ε)*‖u‖) := mul_le_mul_of_nonneg_left hDN (norm_nonneg _)
    _ = _ := by ring

end ShrinkingSpheres
