import Proof.PhysicalPotentialGeneratorBounds
import Proof.ModelPotentialRadiusBudget
import Proof.NormalGeodesicBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def potentialWordEntryBudget (K : ℝ) : ℝ := 100*(K+1)*K^2

def potentialWordWeightedEntry (d : Data) (y : X) (a b : PhysicalPotentialGeneratorIndex) : ℝ :=
  |PhysicalPrincipalData.potentialWordCoefficient d y a b| *
    potentialGeneratorWeight (d.radius y) a*potentialGeneratorWeight (d.radius y) b

def potentialWordMass (d : Data) (y : X) : ℝ :=
  ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,potentialWordWeightedEntry d y a b

/-- Every entry is small after the genuine radius weight of each actual
    first-error generator is included. Only original zero-order h-smallness
    and the admitted profile weights are used. -/
theorem Admissible.potentialWordWeightedEntry_le {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (a b : PhysicalPotentialGeneratorIndex) :
    potentialWordWeightedEntry d y a b ≤ potentialWordEntryBudget K*ε := by
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let f := fun i => fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)
  let t := fun i => scaledFrameLogRadius d.radius d.frame i y
  let r := d.radius y
  let B := 9*(K+1)*K^2
  let C := potentialWordEntryBudget K
  have hK0 := zero_lt_one.trans_le hK
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hr : 0 ≤ r := (hd.2.2.2.2.1.2 y hy).1.le
  have hrP : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hr3 : r^3 ≤ ε := by
    have hr2 : r^2 ≤ r := by nlinarith only [mul_nonneg hr (sub_nonneg.mpr hr1)]
    have hh := mul_le_mul_of_nonneg_left hr2 hr
    nlinarith only [hh,hr2,hrε]
  have h9B : 9*B ≤ C := by
    have hh : 0 ≤ (K+1)*K^2 := by positivity
    change 9*(9*(K+1)*K^2) ≤ 100*(K+1)*K^2
    nlinarith only [hh]
  have h3B : 3*B ≤ C := by linarith only [h9B,hB]
  have hBC : B ≤ C := by linarith only [h9B,hB]
  have hKC : 54*K^2 ≤ C := by
    have hh := mul_le_mul_of_nonneg_right (show 1 ≤ K+1 by linarith only [hK]) (sq_nonneg K)
    change 54*K^2 ≤ 100*(K+1)*K^2
    nlinarith only [hh,sq_nonneg K]
  have hC : 0 ≤ C := hB.trans hBC
  have hQ (i j : I) : |q i j| ≤ B := (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.1
  have ht (i : I) : |t i| ≤ 1 := hd.scaled_frame_logRadius_bound hf hε hε1 hy i
  have hδ (i j : I) : |(q i j-(if i=j then 1 else 0))/r| ≤ 9*K^2*ε :=
    (hd.framePrincipalCoefficient_bounds hK hf hε hε1 hy i j).2.2
  have h3 (v : I → ℝ) (A : ℝ) (hv : ∀ i,|v i| ≤ A) : |∑ i : I,v i| ≤ 3*A := by
    have hh := norm_weighted_sum_three_le (fun _ : I => (1:ℝ)) v 1 A (by norm_num)
      (fun _ => by norm_num) (fun i => by simpa only [Real.norm_eq_abs] using hv i)
    simpa only [one_smul,Real.norm_eq_abs,mul_one] using hh
  have h9 (v : I → I → ℝ) (A : ℝ) (hv : ∀ i j,|v i j| ≤ A) : |∑ i : I,∑ j : I,v i j| ≤ 9*A :=
    (h3 (fun i => ∑ j : I,v i j) (3*A) (fun i => h3 (v i) A (hv i))).trans_eq (by ring)
  have hDD : |∑ i : I,∑ j : I,q i j*(r*f i*f j)| ≤ (9*B)*ε := by
    have hh := h9 (fun i j => q i j*(r*f i*f j)) (B*ε) (fun i j => by
      rw [abs_mul]
      exact mul_le_mul (hQ i j) (hd.radius_frame_logRadius_product_small hy i j) (abs_nonneg _) hB)
    exact hh.trans_eq (by ring)
  have hRD (i : I) : |2*∑ j : I,(q i j-(if i=j then 1 else 0))*f j| ≤ (54*K^2)*ε := by
    have hProduct (j : I) : (q i j-(if i=j then 1 else 0))*f j=
        ((q i j-(if i=j then 1 else 0))/r)*t j := by
      change (q i j-(if i=j then 1 else 0))*f j=
        ((q i j-(if i=j then 1 else 0))/r)*(r*f j)
      rw [← mul_assoc,div_mul_cancel₀ _ hrP.ne']
    have hh := h3 (fun j => (q i j-(if i=j then 1 else 0))*f j) (9*K^2*ε) (fun j => by
      rw [hProduct,abs_mul]
      exact (mul_le_mul (hδ i j) (ht j) (abs_nonneg _) (by positivity)).trans_eq (mul_one _))
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  have hDE (j : I) : |∑ i : I,q i j*t i| ≤ 3*B :=
    h3 (fun i => q i j*t i) B (fun i => by
      rw [abs_mul]
      exact (mul_le_mul (hQ i j) (ht i) (abs_nonneg _) hB).trans_eq (mul_one _))
  have hED (i : I) : |∑ j : I,q i j*t j| ≤ 3*B :=
    h3 (fun j => q i j*t j) B (fun j => by
      rw [abs_mul]
      exact (mul_le_mul (hQ i j) (ht j) (abs_nonneg _) hB).trans_eq (mul_one _))
  have hQR (i j : I) : |q i j| *r ≤ B*ε :=
    (mul_le_mul_of_nonneg_right (hQ i j) hr).trans (mul_le_mul_of_nonneg_left hrε hB)
  rcases a with u | (i | i)
  · rcases b with v | (j | j)
    · simpa only [potentialWordWeightedEntry,PhysicalPrincipalData.potentialWordCoefficient,potentialGeneratorWeight,mul_one]
        using hDD.trans (mul_le_mul_of_nonneg_right h9B hε)
    · simpa only [potentialWordWeightedEntry,PhysicalPrincipalData.potentialWordCoefficient,potentialGeneratorWeight,abs_zero,zero_mul]
        using mul_nonneg hC hε
    · change |∑ k : I,q k j*t k| *1*r ≤ C*ε
      rw [mul_one]
      exact ((mul_le_mul_of_nonneg_right (hDE j) hr).trans
        (mul_le_mul_of_nonneg_left hrε (by positivity))).trans (mul_le_mul_of_nonneg_right h3B hε)
  · rcases b with v | (j | j)
    · simpa only [potentialWordWeightedEntry,PhysicalPrincipalData.potentialWordCoefficient,potentialGeneratorWeight,mul_one]
        using (hRD i).trans (mul_le_mul_of_nonneg_right hKC hε)
    · have hh : |frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j/r| ≤ 9*K^2*ε := by
        rw [frameTensorMatrix_sub,frameTensorMatrix_inverse_metric d.γ d.frame y
          (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy))]
        exact hδ i j
      have h9KC : 9*K^2 ≤ C := (by nlinarith only [sq_nonneg K] : 9*K^2 ≤ 54*K^2).trans hKC
      change |frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y-(d.γ y)⁻¹) i j/r| *1*1 ≤ C*ε
      simpa only [mul_one] using hh.trans (mul_le_mul_of_nonneg_right h9KC hε)
    · change |q i j| *1*r ≤ C*ε
      rw [mul_one]
      exact (hQR i j).trans (mul_le_mul_of_nonneg_right hBC hε)
  · rcases b with v | (j | j)
    · change |∑ k : I,q i k*t k| *r*1 ≤ C*ε
      rw [mul_one]
      exact ((mul_le_mul_of_nonneg_right (hED i) hr).trans
        (mul_le_mul_of_nonneg_left hrε (by positivity))).trans (mul_le_mul_of_nonneg_right h3B hε)
    · change |q i j| *r*1 ≤ C*ε
      rw [mul_one]
      exact (hQR i j).trans (mul_le_mul_of_nonneg_right hBC hε)
    · change |r*q i j| *r*r ≤ C*ε
      rw [abs_mul,abs_of_nonneg hr]
      calc
        _ = |q i j| *r^3 := by ring
        _ ≤ B*r^3 := mul_le_mul_of_nonneg_right (hQ i j) (pow_nonneg hr _)
        _ ≤ B*ε := mul_le_mul_of_nonneg_left hr3 hB
        _ ≤ C*ε := mul_le_mul_of_nonneg_right hBC hε
end ShrinkingSpheres
