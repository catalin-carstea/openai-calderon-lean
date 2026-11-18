import Proof.ParallelNormAssemblyReservedWordPair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The zero-base part of model raising is exactly the raising/degree word
with the actual log-radius coefficients. -/
def modelZeroWordCoefficient (d : Data) (y : X) :
    PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ
  | .inr (.inl i),.inl _ => modelLogRadiusCoefficient d i y
  | _,_ => 0

lemma model_zero_word_mass_eq (d : Data) (y : X) :
    quadraticWordCoefficientMass (modelZeroWordCoefficient d y) (potentialGeneratorWeight (d.radius y))=
      ∑ i : I,|modelLogRadiusCoefficient d i y| := by
  simp [quadraticWordCoefficientMass,modelZeroWordCoefficient,potentialGeneratorWeight,Fintype.sum_sum_type]

lemma model_zero_word_mass_bound (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    quadraticWordCoefficientMass (modelZeroWordCoefficient d y) (potentialGeneratorWeight (d.radius y)) ≤
      3*beta d.γ d.radius y := by
  rw [model_zero_word_mass_eq]
  calc
    _ ≤ ∑ _i : I,beta d.γ d.radius y := Finset.sum_le_sum (fun i _ =>
      frame_logRadius_component_bound d.γ d.frame d.radius y hFrame i)
    _ = _ := by simp only [Fin.sum_univ_three];ring

/-- Actual forward model-zero angular output on the same chosen word core. -/
def modelZeroForwardCoreValue {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (5/2:ℝ)) : SphereSobolev 0 :=
  sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (quadraticWordForwardCoreValue P y (modelZeroWordCoefficient d y) (fun a => W.forwardFirstWordHigherL a u))

def modelZeroAdjointCoreValue {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (5/2:ℝ)) : SphereSobolev 0 :=
  sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (quadraticWordAdjointCoreValue P W (modelZeroWordCoefficient d y) (fun a => W.reverseFirstWordHigherL a u))

lemma first_word_degree_eq {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (5/2:ℝ)) :
    W.forwardFirstWordHigherL (.inl ()) u=sphereSobolevShiftedDegreeL (5/2:ℝ) u := by
  apply sphereSobolevInclusionL_injective (3/2:ℝ) (1/2:ℝ) (by norm_num)
  exact (W.forwardFirstWordHigherL_inclusion hy (.inl ()) u).trans
    (shiftedDegreeFiveHalf_inclusion u).symm

/-- The word-core model output is the literal raising/degree model mass
term, joined by genuine lower endpoint inclusion graphs. -/
lemma model_zero_forward_actual {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (5/2:ℝ)) :
    modelZeroForwardCoreValue P W u=
      ∑ i : I,modelLogRadiusCoefficient d i y • flatRaisingSobolevL 1 i
        (sphereSobolevShiftedDegreeL 2 (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num) u)) := by
  simp only [modelZeroForwardCoreValue,quadraticWordForwardCoreValue,Fintype.sum_sum_type,Fintype.sum_unique,
    modelZeroWordCoefficient,PhysicalPrincipalData.potentialGeneratorHigh,zero_smul,
    Finset.sum_const_zero,add_zero,zero_add,map_sum,map_smul,first_word_degree_eq P hy W u]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hIR : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  have hID : sphereSobolevInclusionL ((5/2:ℝ)-1) ((2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) := by congr 1 <;> norm_num
  have hR := DFunLike.congr_fun (flatRaisingSobolevL_inclusion (3/2:ℝ) 1 (by norm_num) i)
    (sphereSobolevShiftedDegreeL (5/2:ℝ) u)
  rw [hIR] at hR
  have hD := sphereSobolevShiftedDegreeL_inclusion (5/2:ℝ) 2 (by norm_num) u
  rw [hID] at hD
  simpa only [ContinuousLinearMap.comp_apply,flatThreeHalfRaisingL] using hR.symm.trans
    (congrArg (flatRaisingSobolevL 1 i) hD)

/-- One actual mixed potential/model-mass contribution is bounded at the
original epsilon*beta angular mass-energy scale. All word contractions,
actual adjoints and the same W are retained. -/
theorem model_zero_potential_mixed_point_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y)
    (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (W : PhysicalPotentialQuarticData P y CG CK)
    (u : SphereSobolev (5/2:ℝ)) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    |⟪modelZeroForwardCoreValue P W u,P.potentialQuadraticCoreL W u⟫_ℝ-
      ⟪modelZeroAdjointCoreValue P W u,P.potentialQuadraticAdjointCoreL W u⟫_ℝ| ≤
      (12*G^2*CK*(49*potentialWordEntryBudget K))*ε*beta d.γ d.radius y*
        ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u‖^2 := by
  let U := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
  let V := fun a => W.forwardFirstWordHigherL a u
  let v := fun a => W.reverseFirstWordHigherL a u
  have hV := fun a => W.forwardFirstWordHigherL_inclusion hy a u
  have hv := fun a => W.reverseFirstWordHigherL_inclusion a u
  have hr := (hd.2.2.2.2.1.2 y hy).1.le
  have hBase := quadratic_word_mixed_core_bound P hy hr hCG hCK W
    (modelZeroWordCoefficient d y) (PhysicalPrincipalData.potentialWordCoefficient d y) U V v hV hv
  have hEqF : P.potentialQuadraticCoreL W u=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (quadraticWordForwardCoreValue P y (PhysicalPrincipalData.potentialWordCoefficient d y) V) := by
    simp only [PhysicalPrincipalData.potentialQuadraticCoreL,ContinuousLinearMap.comp_apply,
      _root_.sum_apply,_root_.smul_apply,quadraticWordForwardCoreValue,V]
  have hEqA : P.potentialQuadraticAdjointCoreL W u=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (quadraticWordAdjointCoreValue P W (PhysicalPrincipalData.potentialWordCoefficient d y) v) := by
    simp only [PhysicalPrincipalData.potentialQuadraticAdjointCoreL,ContinuousLinearMap.comp_apply,
      _root_.sum_apply,_root_.smul_apply,quadraticWordAdjointCoreValue,v]
  rw [hEqF,hEqA]
  apply hBase.trans
  let G := max (physicalPotentialGeneratorBudget CF) CG
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hβ : 0 ≤ beta d.γ d.radius y := Real.sqrt_nonneg _
  have hP := hd.potentialWordMass_le hK hf hε hε1 hy
  have hP0 := potentialWordMass_nonneg d y hr
  have hM := model_zero_word_mass_bound d y (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy))
  have hProd := mul_le_mul hM hP hP0 (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hβ)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hProd
    (show 0 ≤ 4*G^2*CK by positivity)) (sq_nonneg ‖U‖)
  convert hh using 1 <;> dsimp only [potentialWordMass,potentialWordWeightedEntry,quadraticWordCoefficientMass,G,U] <;> ring

end ShrinkingSpheres.ParallelEnergy
