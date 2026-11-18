import Proof.UniformActualFirstAdjointDegree
import Proof.UniformPhysicalPrincipalData
import Proof.NativeFullHalfResponse
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A single globally smooth degree commutator for every SAME selected
physical frame first error, with a uniform one-radius norm bound. -/
theorem uniform_physical_frame_first_error_degree_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ CF CT : ℝ,∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ S : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∀ i : I,ContDiffOn ℝ ∞ (S i) Y ∧ ∀ x ∈ Y,‖S i x‖ ≤ CD*d.radius x ∧
      ∀ k n : ℕ,∀ z : harmonicSphereSubspace n,
        sphereSobolevCoefficientL (-(1/2:ℝ)) k (S i x (sphereSobolevSingleL (1/2:ℝ) n z))=
          ((k:ℝ)-(n:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) k
            (P.first.low i x (sphereSobolevSingleL (1/2:ℝ) n z)) := by
  classical
  obtain ⟨η,CD,hη,hη1,hCD,hProduce⟩ := uniform_actual_first_adjoint_error_degree hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,3*K*CD,hη,hη1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  choose S hSS hSB using fun a : I => hProduce floor hf ε hε hSmall d hd (axis a) P.radial P.adjoint (P.center a)
    P.radial_actual P.adjoint_pair (P.center_actual a)
  let SF := fun (i : I) (x : X) => ∑ a : I,d.frame x i a • S a x
  refine ⟨SF,?_⟩
  intro i
  have he := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  refine ⟨ContDiffOn.sum (fun a _ => ((EuclideanSpace.proj (𝕜:=ℝ) a).contDiff.comp_contDiffOn he).smul (hSS a)),?_⟩
  intro x hx
  have hFrame := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hNorm : ‖SF i x‖ ≤ (3*K*CD)*d.radius x :=
    (norm_weighted_sum_three_le (fun a => d.frame x i a) (fun a => S a x) K (CD*d.radius x)
      (zero_le_one.trans hK)
      (fun a => hd.1.1.frame_component_abs_le hK d.frame (hSub hx) hFrame i a)
      (fun a => by simpa only [norm_axis,mul_one] using (hSB a x hx).1)).trans_eq (by ring)
  refine ⟨hNorm,?_⟩
  intro k n z
  have hL := half_physical_blocks_of_coarse_compatible _ _ (P.first.low_coarse i x hx) k n z
  rw [hL]
  change sphereSobolevCoefficientL (-(1/2:ℝ)) k ((∑ a : I,d.frame x i a • S a x) (sphereSobolevSingleL (1/2:ℝ) n z))=_
  simp only [_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  calc
    _ = ∑ a : I,d.frame x i a • (((k:ℝ)-(n:ℝ)) •
        coarsePhysicalHarmonicBlock (actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) x) k n z) :=
      Finset.sum_congr rfl (fun a _ => congrArg (fun v : harmonicSphereSubspace k => d.frame x i a • v)
        ((hSB a x hx).2 k n z))
    _ = ((k:ℝ)-(n:ℝ)) • (∑ a : I,d.frame x i a •
        coarsePhysicalHarmonicBlock (actualFirstAdjointErrorFamily d (axis a) P.adjoint (P.center a) x) k n z) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun a _ => smul_comm _ _ _)
    _ = _ := by
      simp only [coarsePhysicalHarmonicBlock,actualFrameFirstAdjointErrorFamily,ContinuousLinearMap.comp_apply,
        _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
end ShrinkingSpheres
