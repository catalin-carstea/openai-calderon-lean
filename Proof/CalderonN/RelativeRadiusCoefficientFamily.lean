module

public import Proof.CalderonN.RelativeRadiusCoefficientJets
public import Proof.CalderonN.NativeCoefficientBallPoisson

import Proof.CalderonN.BallRegularity.CommonSupportMatrix
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim]

/-- An ambient compact coefficient lift is determined by its field,
since its entries encode the derivatives of that field. -/
theorem coefficientMatrixField_injective (k : ℕ) :
    Function.Injective (coefficientMatrixField (dim := dim) k) := by
  intro F G h
  funext i j
  apply Subtype.ext
  funext l
  apply BoundedContinuousFunction.ext
  intro z
  have e : coefficientValue k (F i j) = coefficientValue k (G i j) := by
    funext w
    exact congrArg (fun M : X dim → Mat dim => M w i j) h
  rw [coefficientJet_eq_iteratedFDeriv,coefficientJet_eq_iteratedFDeriv,e]

/-- A compact relative-radius family agrees with the given coefficient
extension at the actual radius and with physical dilation near the unit ball. -/
theorem exists_relativeRadius_coefficientFamily [Nontrivial (Fin dim)]
    (d : Data dim) (y : X dim) (F : SmoothCoefficientMatrix dim 2)
    (hF : EqOn (coefficientMatrixField 2 F)
      (fun z => firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z))
      (ball (0 : X dim) (5/4))) :
    ∃ a : ℝ × X dim → Mat dim, ∃ ha : ContDiff ℝ ∞ a,
      ∃ K : Set (X dim), ∃ hK : IsCompact K,
        ∃ hS : ∀ t z, z ∉ K → a (t,z) = 0,
          commonSupportMatrixFamily 2 a ha K hK hS 0 = F ∧
          ∀ t ∈ ball (0 : ℝ) (1/16), ∀ z ∈ ball (0 : X dim) (9/8),
            a (t,z) = relativeRadiusCoefficient d y t z := by
  let g := coefficientMatrixField 2 F
  obtain ⟨g',hg',S,hS,hgS,hGE,_⟩ := exists_constantFamily_of_coefficientMatrix 2 F
  have hg : ContDiff ℝ ∞ g := by
    rw [hGE] at hg'
    exact hg'.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
  have hgSupp (z : X dim) (hz : z ∉ S) : g z = 0 := by
    simpa only [hGE,Function.comp_apply,g] using hgS 0 z hz
  let χ : ContDiffBump (0 : X dim) := ⟨9/8,5/4,by norm_num,by norm_num⟩
  let a : ℝ × X dim → Mat dim := fun p =>
    g p.2 + χ p.2 • (g ((1+p.1) • p.2)-g p.2)
  have ha : ContDiff ℝ ∞ a :=
    (hg.comp contDiff_snd).add ((χ.contDiff.comp contDiff_snd).smul
      ((hg.comp ((contDiff_const.add contDiff_fst).smul contDiff_snd)).sub (hg.comp contDiff_snd)))
  let K := S ∪ tsupport (χ : X dim → ℝ)
  have hK : IsCompact K := hS.union χ.hasCompactSupport
  have haS (t : ℝ) (z : X dim) (hz : z ∉ K) : a (t,z) = 0 := by
    have hzS : z ∉ S := fun h => hz (Or.inl h)
    have hzχ : z ∉ tsupport (χ : X dim → ℝ) := fun h => hz (Or.inr h)
    change g z+χ z • (g ((1+t) • z)-g z) = 0
    rw [hgSupp z hzS,image_eq_zero_of_notMem_tsupport hzχ,zero_smul,add_zero]
  refine ⟨a,ha,K,hK,haS,?_,?_⟩
  · apply coefficientMatrixField_injective 2
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    funext z
    change g z+χ z • (g ((1+0) • z)-g z) = g z
    simp
  · intro t ht z hz
    have hχ : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
    have hT : ‖(1+t : ℝ)‖ ≤ 17/16 := (norm_add_le _ _).trans
      (by rw [norm_one]; linarith only [(mem_ball_zero_iff.mp ht).le])
    have hW : (1+t) • z ∈ ball (0 : X dim) (5/4) := by
      apply mem_ball_zero_iff.mpr
      rw [norm_smul]
      exact (mul_le_mul hT (mem_ball_zero_iff.mp hz).le (norm_nonneg _) (by norm_num)).trans_lt (by norm_num)
    have he (s : ℝ) : frameVector d.frame y (s • z) = s • frameVector d.frame y z := by
      rw [← frameVectorLinear_apply,map_smul,frameVectorLinear_apply]
    change g z+χ z • (g ((1+t) • z)-g z) = relativeRadiusCoefficient d y t z
    rw [hχ,one_smul,add_sub_cancel]
    change coefficientMatrixField 2 F ((1+t) • z) = relativeRadiusCoefficient d y t z
    rw [hF hW]
    change firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y ((1+t) • z)) = _
    rw [he,smul_smul]
    rfl

end CalderonN
