import Proof.FramedRaisingBilinearExpansion
import Proof.BalancedDoubleRaising
import Proof.PureAngularPrincipalPerturbation
import Proof.FramePrincipalBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine balanced realization of the SAME pure angular h/r coefficient. -/
def pureAngularPrincipalHalfL (d : Data) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ i : I,∑ j : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j/d.radius y) •
    (flatHalfRaisingL i).comp (flatThreeHalfRaisingL j)

lemma pureAngularPrincipalPerturbationL_frame (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    pureAngularPrincipalPerturbationL d y=
      ∑ i : I,∑ j : I,(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j/d.radius y) •
        (flatOneRaisingL i).comp (flatTwoRaisingL j) := by
  have hh := framedFlatRaisingSobolevL_matrix_contraction 2 d.γ d.frame y he
    (fun a b => (principal d.γ d.g₂ y-(d.γ y)⁻¹) a b/d.radius y)
  rw [show (2:ℝ)-1=1 by norm_num] at hh
  simpa only [pureAngularPrincipalPerturbationL,frameTensorMatrix_div,flatOneRaisingL,flatTwoRaisingL] using hh

/-- Exact identification with the physical H2 pure angular coefficient on
    the common core, through the genuine H(-1) inclusion. -/
lemma pureAngularPrincipalHalfL_coarse (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (u : SphereSobolev 2) :
    sphereSobolevInclusionL (-(1/2:ℝ)) (-1:ℝ) (by norm_num)
      (pureAngularPrincipalHalfL d y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u))=
      sphereSobolevInclusionL 0 (-1:ℝ) (by norm_num) (pureAngularPrincipalPerturbationL d y u) := by
  rw [pureAngularPrincipalPerturbationL_frame d y he]
  simp only [pureAngularPrincipalHalfL,_root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_sum,map_smul,flatBalancedDoubleRaising_coarse]

lemma pureAngularPrincipalHalfL_actual (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (u : SphereSobolev 2) :
    pureAngularPrincipalHalfL d y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (pureAngularPrincipalPerturbationL d y u) := by
  apply sphereSobolevInclusionL_injective (-(1/2:ℝ)) (-1:ℝ) (by norm_num)
  rw [pureAngularPrincipalHalfL_coarse d y he,sphereSobolevInclusionL_trans_apply]

lemma Admissible.norm_pureAngularPrincipalHalfL_small {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    ‖pureAngularPrincipalHalfL d y‖ ≤ 8100*K^2*radialDriftSobolevBound (-(1/2:ℝ))*
      radialDriftSobolevBound (-(3/2:ℝ))*ε := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hCoeff (i j : I) :
      |frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j/d.radius y| ≤ 9*K^2*ε := by
    rw [frameTensorMatrix_sub,frameTensorMatrix_inverse_metric d.γ d.frame y hFrame]
    exact (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.2
  have hBlo : 0 ≤ radialDriftSobolevBound (-(1/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hBhi : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hTerm (i j : I) :
      ‖(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j/d.radius y) •
        (flatHalfRaisingL i).comp (flatThreeHalfRaisingL j)‖ ≤
      900*K^2*radialDriftSobolevBound (-(1/2:ℝ))*radialDriftSobolevBound (-(3/2:ℝ))*ε := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (9*K^2*ε)*(‖flatHalfRaisingL i‖*‖flatThreeHalfRaisingL j‖) :=
        mul_le_mul (hCoeff i j) (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ (9*K^2*ε)*((10*radialDriftSobolevBound (-(1/2:ℝ)))*(10*radialDriftSobolevBound (-(3/2:ℝ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (norm_flatHalfRaisingL_le i) (norm_flatThreeHalfRaisingL_le j)
          (norm_nonneg _) (mul_nonneg (by norm_num) hBlo)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ i : I,∑ j : I,‖(frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j/d.radius y) •
        (flatHalfRaisingL i).comp (flatThreeHalfRaisingL j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : I,∑ _j : I,900*K^2*radialDriftSobolevBound (-(1/2:ℝ))*radialDriftSobolevBound (-(3/2:ℝ))*ε :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTerm i j))
    _ = _ := by simp only [Fin.sum_univ_three];ring

lemma Admissible.contDiffOn_pureAngularPrincipalHalfL {Y Ω : Set X} (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (pureAngularPrincipalHalfL d) Y := by
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have h₂ : Elliptic Y K d.g₂ := ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hEntries (a b : I) : ContDiffOn ℝ ∞ (fun x => (principal d.γ d.g₂ x-(d.γ x)⁻¹) a b) Y := by
    simpa only [Matrix.sub_apply] using (contDiffOn_principal_entry h h₂ hK a b).sub (h.contDiffOn_inverse_entry hK a b)
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  have hTensor := contDiffOn_frameTensorMatrix d.γ d.frame h
    (fun k => (hd.1.2.2.2.2.2.2.1 k).mono hSub) (fun x => principal d.γ d.g₂ x-(d.γ x)⁻¹) hEntries i j
  exact (hTensor.div hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')).smul contDiffOn_const

end ShrinkingSpheres
