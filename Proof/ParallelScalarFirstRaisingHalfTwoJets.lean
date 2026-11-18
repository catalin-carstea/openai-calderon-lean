import Proof.FramedRaisingStrongHalfJet
import Proof.UniformFramedRaisingCoarseTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def framedRaisingSecondHalfJet (d : Data) (i j b : I) (x : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ a : I,(christoffel d.γ x a i b • framedRaisingFirstHalfJet d j a x+
    fderiv ℝ (fun y => christoffel d.γ y a i b) x (axis j) • framedRaisingHalfL d x (axis a))

lemma framedRaisingSecondHalfJet_coarse (d : Data) (i j b : I) (x : X) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (framedRaisingSecondCoarseJet d i j b x)=
      (framedRaisingSecondHalfJet d i j b x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have h0 (a : I) := DFunLike.congr_fun (framedRaisingHalfL_coarse d x (axis a)) u
  have h1 (a : I) := DFunLike.congr_fun (framedRaisingFirstHalfJet_coarse d j a x) u
  simp only [ContinuousLinearMap.comp_apply] at h0 h1
  simp only [framedRaisingSecondCoarseJet,framedRaisingSecondHalfJet,
    ← framedRaisingFirstCoarseJet_eq,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.add_apply,_root_.smul_apply,map_sum,map_add,map_smul,h0,h1]

lemma framedRaisingFirstHalfJet_smooth {Y Ω : Set X}
    (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (i b : I) :
    ContDiffOn ℝ ∞ (framedRaisingFirstHalfJet d i b) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  exact ContDiffOn.sum (fun a _ =>
    ((hd.1.1.contDiffOn_christoffel hΩ hK a i b).mono hSub).smul
      (hd.framedRaisingHalf_smooth (axis a)).1)

/-- The actual strong half raising jets through two have common metric
bounds, with no quantitative hypothesis on the chosen frame derivatives. -/
theorem uniform_framed_raising_strong_half_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ,0 ≤ Q ∧ ∀ floor ε : ℝ,∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j b : I,
        ‖framedRaisingHalfL d y (axis b)‖ ≤ Q ∧
        ‖framedRaisingFirstHalfJet d i b y‖ ≤ Q ∧
        ‖framedRaisingSecondHalfJet d i j b y‖ ≤ Q := by
  obtain ⟨Q0,hQ0,hOne⟩ := uniform_framed_raising_strong_half_one_jet hY hΩ (by omega) K ρ c₀ M Cj hK
  let M1 := |M ⟨1,by omega⟩|
  let M2 := |M ⟨2,by omega⟩|
  let G := 9*K*M1
  let D := 81*K^2*M1^2+9*K*M2
  let T := 3*(G*Q0+D*Q0)
  let Q := Q0+T
  have hG : 0 ≤ G := by dsimp only [G,M1];positivity
  have hD : 0 ≤ D := by dsimp only [D,M1,M2];positivity
  have hT : 0 ≤ T := by dsimp only [T];positivity
  refine ⟨Q,by dsimp only [Q];positivity,?_⟩
  intro floor ε d hd y hy i j b
  have hyΩ := hd.2.1.center_mem hy
  have hMetric1 (a c : I) : ‖fderiv ℝ (fun x => d.γ x a c) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound (by omega) hyΩ a c).trans (le_abs_self _)
  have hMetric2 (a c : I) : ‖fderiv ℝ (fderiv ℝ (fun x => d.γ x a c)) y‖ ≤ M2 :=
    (hd.1.reference_second_fderiv_bound hm hyΩ a c).trans (le_abs_self _)
  have hGamma (a : I) : |christoffel d.γ y a i b| ≤ G :=
    hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) hyΩ M1 (abs_nonneg _) hMetric1 a i b
  have hGammaD (a : I) : |fderiv ℝ (fun x => christoffel d.γ x a i b) y (axis j)| ≤ D := by
    simpa only [norm_axis,mul_one] using
      hd.1.1.christoffel_derivative_entry_bound hΩ (zero_lt_one.trans_le hK) hyΩ
        M1 M2 (abs_nonneg _) (abs_nonneg _) hMetric1 hMetric2 (axis j) a i b
  have hSecond : ‖framedRaisingSecondHalfJet d i j b y‖ ≤ T := by
    have hTerm (a : I) : ‖christoffel d.γ y a i b • framedRaisingFirstHalfJet d j a y+
        fderiv ℝ (fun x => christoffel d.γ x a i b) y (axis j) • framedRaisingHalfL d y (axis a)‖ ≤ G*Q0+D*Q0 := by
      have h0 : ‖christoffel d.γ y a i b • framedRaisingFirstHalfJet d j a y‖ ≤ G*Q0 := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hGamma a) ((hOne floor ε d hd y hy j a).2) (norm_nonneg _) hG
      have h1 : ‖fderiv ℝ (fun x => christoffel d.γ x a i b) y (axis j) • framedRaisingHalfL d y (axis a)‖ ≤ D*Q0 := by
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hGammaD a) ((hOne floor ε d hd y hy j a).1) (norm_nonneg _) hD
      exact (norm_add_le _ _).trans (add_le_add h0 h1)
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun a _ => hTerm a)).trans_eq
      (by simp only [Fin.sum_univ_three,T];ring))
  refine ⟨((hOne floor ε d hd y hy i b).1).trans (le_add_of_nonneg_right hT),
    ((hOne floor ε d hd y hy i b).2).trans (le_add_of_nonneg_right hT),?_⟩
  exact hSecond.trans (by dsimp only [Q];linarith only [hQ0])

end ShrinkingSpheres.ParallelEnergy
