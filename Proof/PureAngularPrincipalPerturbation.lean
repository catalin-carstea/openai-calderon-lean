import Proof.FramedFlatRaisingTrace
import Proof.Smallness
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The concrete pure angular second-order perturbation (h/r) A* A* in
    ordinary base coordinates, using the actual metric coframe. -/
def pureAngularPrincipalPerturbationL (d : Data) (y : X) :
    SphereSobolev 2 →L[ℝ] SphereSobolev 0 :=
  ∑ a : I,∑ b : I,((principal d.γ d.g₂ y-(d.γ y)⁻¹) a b/d.radius y) •
    (framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)).comp
      (framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b))

lemma Admissible.norm_pureAngularPrincipalPerturbationL_le {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hε : 0 ≤ ε)
    {y : X} (hy : y ∈ Y) :
    ‖pureAngularPrincipalPerturbationL d y‖ ≤ 6480*(9*|M 0| *K)^2*ε := by
  let C := 9*|M 0| *K
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hRatio (a b : I) : |(principal d.γ d.g₂ y-(d.γ y)⁻¹) a b/d.radius y| ≤ ε := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_iff₀ hr).2 (hd.2.2.2.2.2.component_bound hy a b)
  have hN1 (a : I) : ‖framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)‖ ≤ 6*C := by
    simpa only [norm_axis,mul_one] using (hd.framedFlatRaisingSobolevL_norms hK hy (axis a)).1
  have hN2 (a : I) : ‖framedFlatRaisingSobolevL 2 d.γ d.frame y (axis a)‖ ≤ 120*C := by
    simpa only [norm_axis,mul_one] using (hd.framedFlatRaisingSobolevL_norms hK hy (axis a)).2
  have hTerm (a b : I) :
      ‖((principal d.γ d.g₂ y-(d.γ y)⁻¹) a b/d.radius y) •
        (framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)).comp
          (framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b))‖ ≤ 720*C^2*ε := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ ε*(‖framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)‖*
        ‖framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b)‖) :=
        mul_le_mul (hRatio a b) (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) hε
      _ ≤ ε*((6*C)*(120*C)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hN1 a) (hN2 b) (norm_nonneg _) (by positivity)) hε
      _ = _ := by ring
  calc
    _ ≤ ∑ a : I,‖∑ b : I,((principal d.γ d.g₂ y-(d.γ y)⁻¹) a b/d.radius y) •
        (framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)).comp
          (framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b))‖ := norm_sum_le _ _
    _ ≤ ∑ a : I,∑ b : I,‖((principal d.γ d.g₂ y-(d.γ y)⁻¹) a b/d.radius y) •
        (framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)).comp
          (framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b))‖ := Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : I,∑ _b : I,720*C^2*ε := Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hTerm a b))
    _ = _ := by simp only [Fin.sum_univ_three];dsimp only [C];ring

/-- The displayed coefficient is exactly the radius-scaled product of the
    two inverse-radius leading adjoint terms contracted with h. -/
lemma pureAngularPrincipalPerturbationL_exact (d : Data) (y : X) (hr : d.radius y ≠ 0) :
    d.radius y • (∑ a : I,∑ b : I,(principal d.γ d.g₂ y-(d.γ y)⁻¹) a b •
      ((d.radius y)⁻¹ • framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)).comp
        ((d.radius y)⁻¹ • framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b)))=
      pureAngularPrincipalPerturbationL d y := by
  simp only [pureAngularPrincipalPerturbationL,Finset.smul_sum,ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul,smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  field_simp [hr]
/-- The entire pure-angular leading product contracted with the actual
    normalized principal matrix is exactly its small h/r perturbation. -/
theorem pureAngularPrincipalPerturbationL_principal_exact (d : Data) (y : X)
    (hr : d.radius y ≠ 0)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    d.radius y • (∑ a : I,∑ b : I,principal d.γ d.g₂ y a b •
      ((d.radius y)⁻¹ • framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)).comp
        ((d.radius y)⁻¹ • framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b)))=
      pureAngularPrincipalPerturbationL d y := by
  let R (a b : I) : SphereSobolev 2 →L[ℝ] SphereSobolev 0 := (framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a)).comp
    (framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b))
  have hOrder : (2:ℝ)-1=1 := by norm_num
  have hLow (a : I) : framedFlatRaisingSobolevL ((2:ℝ)-1) d.γ d.frame y (axis a)=
      framedFlatRaisingSobolevL 1 d.γ d.frame y (axis a) := by rw [hOrder]
  have hZero : (∑ a : I,∑ b : I,(d.γ y)⁻¹ a b • R a b)=0 := by
    have hh := framedFlatRaisingSobolevL_inverse_metric_contracted_zero 2 d.γ d.frame y he
    have hEq : (∑ a : I,∑ b : I,(d.γ y)⁻¹ a b • R a b)=
        ∑ a : I,∑ b : I,(d.γ y)⁻¹ a b •
          (framedFlatRaisingSobolevL ((2:ℝ)-1) d.γ d.frame y (axis a)).comp
            (framedFlatRaisingSobolevL 2 d.γ d.frame y (axis b)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hLow]
    exact hEq.trans hh
  have hSplit : (∑ a : I,∑ b : I,principal d.γ d.g₂ y a b • R a b)=
      ∑ a : I,∑ b : I,(principal d.γ d.g₂ y-(d.γ y)⁻¹) a b • R a b := by
    have hh : (∑ a : I,∑ b : I,(principal d.γ d.g₂ y-(d.γ y)⁻¹) a b • R a b)=
        (∑ a : I,∑ b : I,principal d.γ d.g₂ y a b • R a b)-
          (∑ a : I,∑ b : I,(d.γ y)⁻¹ a b • R a b) := by
      simp only [Matrix.sub_apply,sub_smul,Finset.sum_sub_distrib]
    rw [hZero,sub_zero] at hh
    exact hh.symm
  calc
    _ = (d.radius y)⁻¹ • (∑ a : I,∑ b : I,principal d.γ d.g₂ y a b • R a b) := by
      simp only [Finset.smul_sum,ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_smul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      change (d.radius y*(principal d.γ d.g₂ y a b*((d.radius y)⁻¹*(d.radius y)⁻¹))) • R a b=
        ((d.radius y)⁻¹*principal d.γ d.g₂ y a b) • R a b
      apply congrArg (fun t : ℝ => t • R a b)
      field_simp [hr]
    _ = (d.radius y)⁻¹ • (∑ a : I,∑ b : I,(principal d.γ d.g₂ y-(d.γ y)⁻¹) a b • R a b) := congrArg ((d.radius y)⁻¹ • ·) hSplit
    _ = _ := by
      simp only [pureAngularPrincipalPerturbationL,Finset.smul_sum,smul_smul,div_eq_mul_inv,R]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      ring

end ShrinkingSpheres
