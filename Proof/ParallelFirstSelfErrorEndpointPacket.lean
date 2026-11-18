import Proof.ParallelFirstSelfAdjointTransfer
import Proof.ParallelFirstSelfAdjointEndpointSelection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Fixed actual native-error operator data and their genuine selected
endpoints. This packages hypotheses; it adds no regularity or norm premise. -/
structure FirstSelfActualErrorEndpointPacket (Y : Set X) (d : Data) (a : X) where
  radial : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  adjoint : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  center : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  low : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  high : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  adjoint_smooth : ContDiffOn ℝ ∞ adjoint Y
  center_smooth : ContDiffOn ℝ ∞ center Y
  low_smooth : ContDiffOn ℝ ∞ low Y
  radial_actual : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (radial x)
  adjoint_actual : ∀ x ∈ Y,∀ u v : SphereSobolev 1,
    ⟪(radial x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,adjoint x v⟫_ℝ
  center_actual : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (adjoint x) (center x)
  low_graph : ∀ x ∈ Y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
    (actualFirstAdjointErrorFamily d a adjoint center x)=
      (low x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  high_graph : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (high x)=
    (actualFirstAdjointErrorFamily d a adjoint center x).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))

/-- Select one true-adjoint HIGH family, before derivative directions or
tests, for ANY already fixed compatible actual endpoint packet. -/
theorem uniform_actual_error_adjoint_endpoint_family
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ a : X,
      ∀ p : FirstSelfActualErrorEndpointPacket Y d a,
      ∃ AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        ∀ y ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH y)=
          (p.low y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
          ‖AH y‖ ≤ C*‖a‖*d.radius y := by
  obtain ⟨η,C,hη,hη1,hC,hAdj⟩ := uniform_actual_first_error_adjoint_higher_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd a p
  apply exists_half_adjoint_higher_family p.low (fun y => C*‖a‖*d.radius y)
  intro y hy
  exact hAdj floor hf ε hε hSmall d hd a p.radial p.adjoint p.center
    p.radial_actual p.adjoint_actual p.center_actual y hy (p.low y) (p.low_graph y hy)

/-- Typed point transport avoids re-elaborating the full uniform endpoint
selection theorem when adding a covariant derivative to this SAME family. -/
lemma FirstSelfActualErrorEndpointPacket.true_adjoint_jet_at
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε CE : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y a : X} (hy : y ∈ Y) (p : FirstSelfActualErrorEndpointPacket Y d a)
    (q : FirstSelfNativeAdjointPacket Y Ω d y a CE ε)
    (AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hAH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH y)=
      (p.low y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (b : X) (hb : ‖b‖ ≤ 1) :
    ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      halfOperatorCovariantDerivativeL d (fun x => (p.low x).adjoint) AH y b=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H ∧
      ‖H‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y ∧ ‖H‖ ≤ CE*‖a‖*ε := by
  exact q.physical_transfer hY hΩ hSub hd hK hy p.radial p.adjoint p.center
    p.adjoint_smooth p.center_smooth p.radial_actual p.adjoint_actual p.center_actual p.low p.high AH
    (p.low_smooth.contDiffAt (hY.mem_nhds hy)) p.low_graph (p.high_graph y hy) hAH b hb

end ShrinkingSpheres.ParallelEnergy
