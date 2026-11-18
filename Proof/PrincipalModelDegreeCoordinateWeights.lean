import Proof.AdmissibleRadiusSmallJets
import Proof.PrincipalAdjointBudgetDefinitions
import Proof.BackgroundBudgets
import Proof.NormalGeodesicBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.PrincipalCommutator

def principalModelDegreeCoordinateWeight (d : Data) (b : I) (x : X) : ℝ :=
  ∑ a : I,(principal d.γ d.g₂ x a b+principal d.γ d.g₂ x b a)*coordDeriv a d.radius x

def principalModelDegreeCoordinateBudget (K M1 C2 : ℝ) : ℝ :=
  6*(K*(K+1)+K*(9*K^2*|M1|+1)+(K+1)*(K^2+9*K^2*|C2|+27*K^2*|M1|))

lemma principalModelDegreeCoordinateBudget_nonneg (K M1 C2 : ℝ) (hK : 0 ≤ K) :
    0 ≤ principalModelDegreeCoordinateBudget K M1 C2 := by
  unfold principalModelDegreeCoordinateBudget
  positivity

lemma Admissible.contDiffOn_principalModelDegreeCoordinateWeight {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (b : I) :
    ContDiffOn ℝ ∞ (principalModelDegreeCoordinateWeight d b) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  exact ContDiffOn.sum (fun a _ => ((contDiffOn_principal_entry hg hg2 hK a b).add
    (contDiffOn_principal_entry hg hg2 hK b a)).mul
      ((hd.2.2.2.2.1.1.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const))

/-- The degree coordinate coefficient is small for every admitted profile.
Only the reference metric first jet and the profile Hessian budget occur. -/
theorem Admissible.principalModelDegreeCoordinateWeight_bounds {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} (hm : 1 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (b i : I) :
    let B := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
    |principalModelDegreeCoordinateWeight d b y| ≤ B*ε/beta d.γ d.radius y ∧
      |directionalFDeriv (axis i) (principalModelDegreeCoordinateWeight d b) y| ≤ B*ε := by
  let M1 := |M ⟨1,by omega⟩|
  let A0 := K+1
  let A1 := 9*K^2*M1+1
  let R2 := K^2+9*K^2*|Cj 2|+27*K^2*M1
  let B := principalModelDegreeCoordinateBudget K (M ⟨1,by omega⟩) (Cj 2)
  let β := beta d.γ d.radius y
  have hK0 := zero_lt_one.trans_le hK
  have hM1 : 0 ≤ M1 := abs_nonneg _
  have hA0 : 0 ≤ A0 := by dsimp only [A0];positivity
  have hA1 : 0 ≤ A1 := by dsimp only [A1];positivity
  have hR2 : 0 ≤ R2 := by dsimp only [R2];positivity
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ := ⟨fun j k => (hd.1.1.1 j k).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ := ⟨fun j k => (hd.1.2.2.1.1 j k).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have hDg (a c : I) : ‖fderiv ℝ (fun x => d.γ x a c) y‖ ≤ M1 :=
    (hd.1.reference_fderiv_bound hm (hSub hy) a c).trans (le_abs_self _)
  have hp := hd.2.2.2.2.1
  have hs := hd.2.2.2.2.2
  have hRadS (a : I) : ContDiffOn ℝ ∞ (coordDeriv a d.radius) Y :=
    (hp.1.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have hr := (hp.2 y hy).1
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  have hβP : 0 < β := zero_lt_one.trans_le hβ
  have hr1 := ((radius_bounds (d.radius y) β floor ε hr.le hf (hp.2 y hy).2.1 (hs y hy).2).2.2).trans hε1
  have her : ε*d.radius y ≤ 1 := (mul_le_mul_of_nonneg_right hε1 hr.le).trans (by simpa only [one_mul] using hr1)
  have hP (a c : I) : |principal d.γ d.g₂ y a c| ≤ A0 :=
    (principal_entry_le_inverse_add hg hK0 hs hy a c).trans (by dsimp only [A0];linarith only [her])
  have hDP (a c : I) : |coordDeriv i (fun x => principal d.γ d.g₂ x a c) y| ≤ A1 :=
    (principal_derivative_le_inverse_add hY hg hg2 hK0 hs hy M1 hM1 hDg a c i).trans
      (by dsimp only [A1];linarith only [her])
  have hDr (a : I) : |coordDeriv a d.radius y| ≤ K*ε/β :=
    (hd.coordinate_radius_two_small_jet_bounds hY hm hK hf hy a i).1
  have hDr0 (a : I) : |coordDeriv a d.radius y| ≤ K*ε :=
    (hDr a).trans (div_le_self (mul_nonneg hK0.le hε) hβ)
  have hDDr (a : I) : |coordDeriv i (coordDeriv a d.radius) y| ≤ R2*ε :=
    (hd.coordinate_radius_two_small_jet_bounds hY hm hK hf hy a i).2
  let f := fun (a : I) (x : X) => (principal d.γ d.g₂ x a b+principal d.γ d.g₂ x b a)*coordDeriv a d.radius x
  have hS (a : I) : |principal d.γ d.g₂ y a b+principal d.γ d.g₂ y b a| ≤ 2*A0 :=
    (abs_add_le _ _).trans ((add_le_add (hP a b) (hP b a)).trans_eq (by ring))
  have hEach (a : I) : |f a y| ≤ (2*A0*K)*ε/β := by
    calc
      _ = |principal d.γ d.g₂ y a b+principal d.γ d.g₂ y b a| *|coordDeriv a d.radius y| := abs_mul _ _
      _ ≤ (2*A0)*(K*ε/β) := mul_le_mul (hS a) (hDr a) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hDer (a : I) : directionalFDeriv (axis i) (f a) y=
      (coordDeriv i (fun x => principal d.γ d.g₂ x a b) y+coordDeriv i (fun x => principal d.γ d.g₂ x b a) y)*coordDeriv a d.radius y+
      (principal d.γ d.g₂ y a b+principal d.γ d.g₂ y b a)*coordDeriv i (coordDeriv a d.radius) y := by
    have hp1 := ((contDiffOn_principal_entry hg hg2 hK0 a b).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have hp2 := ((contDiffOn_principal_entry hg hg2 hK0 b a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have hdr : DifferentiableAt ℝ (coordDeriv a d.radius) y := ((hRadS a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have hProd := (hp1.hasFDerivAt.fun_add hp2.hasFDerivAt).fun_mul hdr.hasFDerivAt
    unfold f directionalFDeriv
    rw [hProd.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,coordDeriv]
    ring

  have hDEach (a : I) : |directionalFDeriv (axis i) (f a) y| ≤ (2*A1*K+2*A0*R2)*ε := by
    rw [hDer]
    have hDS := (abs_add_le _ _).trans ((add_le_add (hDP a b) (hDP b a)).trans_eq (by ring : A1+A1=2*A1))
    have h1 : |(coordDeriv i (fun x => principal d.γ d.g₂ x a b) y+coordDeriv i (fun x => principal d.γ d.g₂ x b a) y)*coordDeriv a d.radius y| ≤ 2*A1*(K*ε) := by
      rw [abs_mul];exact mul_le_mul hDS (hDr0 a) (abs_nonneg _) (by positivity)
    have h2 : |(principal d.γ d.g₂ y a b+principal d.γ d.g₂ y b a)*coordDeriv i (coordDeriv a d.radius) y| ≤ 2*A0*(R2*ε) := by
      rw [abs_mul];exact mul_le_mul (hS a) (hDDr a) (abs_nonneg _) (by positivity)
    exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans_eq (by ring)
  have hB0 : 6*A0*K ≤ B := by
    change 6*A0*K ≤ 6*(K*A0+K*A1+A0*R2)
    nlinarith only [mul_nonneg hK0.le hA1,mul_nonneg hA0 hR2]
  have hB1 : 3*(2*A1*K+2*A0*R2) ≤ B := by
    change 3*(2*A1*K+2*A0*R2) ≤ 6*(K*A0+K*A1+A0*R2)
    nlinarith only [mul_nonneg hK0.le hA0]
  refine ⟨?_,?_⟩
  · have ht := (Finset.abs_sum_le_sum_abs (fun a => f a y) Finset.univ).trans
      (Finset.sum_le_sum (fun a _ => hEach a))
    have ht' : |principalModelDegreeCoordinateWeight d b y| ≤ (6*A0*K)*ε/β := by
      change |∑ a : I,f a y| ≤ (6*A0*K)*ε/β
      exact ht.trans_eq (by simp only [Fin.sum_univ_three];ring)
    exact ht'.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hB0 hε) hβP.le)
  · have hDiff (a : I) : DifferentiableAt ℝ (f a) y := by
      exact ((((contDiffOn_principal_entry hg hg2 hK0 a b).add (contDiffOn_principal_entry hg hg2 hK0 b a)).mul
        (hRadS a)).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have hSum : directionalFDeriv (axis i) (principalModelDegreeCoordinateWeight d b) y=
        ∑ a : I,directionalFDeriv (axis i) (f a) y := by
      unfold principalModelDegreeCoordinateWeight directionalFDeriv
      rw [fderiv_fun_sum (fun a _ => hDiff a)]
      rfl
    rw [hSum]
    have ht := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans (Finset.sum_le_sum (fun a _ => hDEach a))
    have ht' : |∑ a : I,directionalFDeriv (axis i) (f a) y| ≤ (3*(2*A1*K+2*A0*R2))*ε := by
      exact ht.trans_eq (by simp only [Fin.sum_univ_three];ring)
    exact ht'.trans (mul_le_mul_of_nonneg_right hB1 hε)
end ShrinkingSpheres
