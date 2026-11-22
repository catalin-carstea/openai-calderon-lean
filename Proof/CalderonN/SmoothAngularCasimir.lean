module

public import Proof.CalderonN.SmoothSphereRotation
public import Proof.CalderonN.RotationCasimir
public import Proof.CalderonN.EuclideanPolynomialEvaluation
public import Proof.CalderonN.HarmonicHilbertDecomposition

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

@[expose] public section

/- Port of the smooth Casimir expansion from Proposition 5.3 check f308cb9d. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace CalderonN
open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation AngularPolynomial GreenRadialTrace

variable {n : ℕ}

 
def angularCasimir (F : (CalderonN.X n) → ℝ) (x : (CalderonN.X n)) : ℝ :=
  -(1/2 : ℝ) * ∑ i : Fin n, ∑ j : Fin n,
    sphereRotationDerivative i j (sphereRotationDerivative i j F) x

 
def shiftedAngularCasimir (F : (CalderonN.X n) → ℝ) (x : (CalderonN.X n)) : ℝ := F x + angularCasimir F x

def shiftedAngularCasimirIterate : ℕ → ((CalderonN.X n) → ℝ) → (CalderonN.X n) → ℝ
  | 0,F => F
  | m+1,F => shiftedAngularCasimir (shiftedAngularCasimirIterate m F)

lemma contDiff_angularCasimir (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (angularCasimir F) := by
  have hsum : ContDiff ℝ ∞ (fun x => ∑ i : Fin n, ∑ j : Fin n,
      sphereRotationDerivative i j (sphereRotationDerivative i j F) x) :=
    ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      contDiff_sphereRotationDerivative i j _ (contDiff_sphereRotationDerivative i j F hF)
  exact contDiff_const.mul hsum

lemma contDiff_shiftedAngularCasimir (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (shiftedAngularCasimir F) := hF.add (contDiff_angularCasimir F hF)

lemma contDiff_shiftedAngularCasimirIterate (m : ℕ) (F : (CalderonN.X n) → ℝ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (shiftedAngularCasimirIterate m F) := by
  induction m with
  | zero => exact hF
  | succ m hm => exact contDiff_shiftedAngularCasimir _ hm

def smoothSphereRestriction (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) : C(UnitSphere n,ℝ) :=
  ⟨fun u => F u.val,hF.continuous.comp continuous_subtype_val⟩

variable [NeZero n]

def smoothSphereLift (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) : SphereL2 n :=
  ContinuousMap.toLp 2 (unitSphereProbability n) ℝ (smoothSphereRestriction F hF)

lemma smoothSphereLift_inner (F G : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) :
    ⟪smoothSphereLift F hF,smoothSphereLift G hG⟫_ℝ =
      ∫ u : UnitSphere n, F u.val * G u.val ∂(unitSphereProbability n) := by
  simpa only [smoothSphereLift,smoothSphereRestriction,ContinuousMap.coe_mk,
    starRingEnd_apply,star_trivial,mul_comm] using
      ContinuousMap.inner_toLp (unitSphereProbability n) (smoothSphereRestriction F hF)
        (smoothSphereRestriction G hG)

lemma smoothSphereLift_add (F G : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) :
    smoothSphereLift (fun x => F x+G x) (hF.add hG) =
      smoothSphereLift F hF + smoothSphereLift G hG := by
  unfold smoothSphereLift
  rw [← map_add]
  congr 1

lemma smoothSphereLift_angularCasimir (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    smoothSphereLift (angularCasimir F) (contDiff_angularCasimir F hF) =
      -(1/2 : ℝ) • ∑ i : Fin n, ∑ j : Fin n,
        smoothSphereLift (sphereRotationDerivative i j (sphereRotationDerivative i j F))
          (contDiff_sphereRotationDerivative i j _
            (contDiff_sphereRotationDerivative i j F hF)) := by
  let f : Fin n → Fin n → C(UnitSphere n,ℝ) := fun i j =>
    smoothSphereRestriction (sphereRotationDerivative i j (sphereRotationDerivative i j F))
      (contDiff_sphereRotationDerivative i j _ (contDiff_sphereRotationDerivative i j F hF))
  have hc : smoothSphereRestriction (angularCasimir F) (contDiff_angularCasimir F hF) =
      -(1/2 : ℝ) • ∑ i : Fin n, ∑ j : Fin n, f i j := by
    ext u
    simp [smoothSphereRestriction,angularCasimir,f]
  unfold smoothSphereLift
  rw [hc]
  simp only [map_smul,map_sum,f]

lemma smoothSphereLift_shiftedAngularCasimir (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    smoothSphereLift (shiftedAngularCasimir F) (contDiff_shiftedAngularCasimir F hF) =
      smoothSphereLift F hF + smoothSphereLift (angularCasimir F) (contDiff_angularCasimir F hF) :=
  smoothSphereLift_add F (angularCasimir F) hF (contDiff_angularCasimir F hF)

lemma inner_sphereRotationDerivative_skew (i j : Fin n) (F G : (CalderonN.X n) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ⟪smoothSphereLift (sphereRotationDerivative i j F)
        (contDiff_sphereRotationDerivative i j F hF),smoothSphereLift G hG⟫_ℝ =
      -⟪smoothSphereLift F hF,smoothSphereLift (sphereRotationDerivative i j G)
        (contDiff_sphereRotationDerivative i j G hG)⟫_ℝ := by
  simp_rw [smoothSphereLift_inner]
  exact integral_sphereRotationDerivative_skew i j F G hF hG

lemma inner_angularCasimir_symmetric (F G : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) :
    ⟪smoothSphereLift (angularCasimir F) (contDiff_angularCasimir F hF),smoothSphereLift G hG⟫_ℝ =
      ⟪smoothSphereLift F hF,smoothSphereLift (angularCasimir G) (contDiff_angularCasimir G hG)⟫_ℝ := by
  rw [smoothSphereLift_angularCasimir F hF,smoothSphereLift_angularCasimir G hG]
  rw [real_inner_smul_left _ (smoothSphereLift G hG) (-(1/2 : ℝ)),
    real_inner_smul_right (smoothSphereLift F hF) _ (-(1/2 : ℝ))]
  simp only [sum_inner,inner_sum]
  apply congrArg (fun t : ℝ => -(1/2 : ℝ) * t)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h1 := inner_sphereRotationDerivative_skew i j (sphereRotationDerivative i j F) G
    (contDiff_sphereRotationDerivative i j F hF) hG
  have h2 := inner_sphereRotationDerivative_skew i j F (sphereRotationDerivative i j G) hF
    (contDiff_sphereRotationDerivative i j G hG)
  linarith

lemma inner_shiftedAngularCasimir_symmetric (F G : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) :
    ⟪smoothSphereLift (shiftedAngularCasimir F) (contDiff_shiftedAngularCasimir F hF),
      smoothSphereLift G hG⟫_ℝ =
    ⟪smoothSphereLift F hF,smoothSphereLift (shiftedAngularCasimir G)
      (contDiff_shiftedAngularCasimir G hG)⟫_ℝ := by
  rw [smoothSphereLift_shiftedAngularCasimir,smoothSphereLift_shiftedAngularCasimir,
    inner_add_left,inner_add_right,inner_angularCasimir_symmetric]

lemma contDiff_polynomialEvaluation (p : MvPolynomial (Fin n) ℝ) :
    ContDiff ℝ ∞ (polynomialEvaluation p) := by
  unfold polynomialEvaluation
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [eval_C] using (contDiff_const : ContDiff ℝ ∞ (fun _ : (CalderonN.X n) => c))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
      convert! hp.mul (contDiff_piLp_apply (p := (2 : ℝ≥0∞)) (i := i)) using 1 <;>
        simp only [map_mul,eval_X,euclideanCoordinates] <;> rfl

lemma sphereRotationDerivative_polynomialEvaluation (i j : Fin n)
    (p : MvPolynomial (Fin n) ℝ) :
    sphereRotationDerivative i j (polynomialEvaluation p) =
      polynomialEvaluation (polynomialRotation i j p) := by
  funext x
  rw [sphereRotationDerivative,fderiv_polynomialEvaluation_apply]
  simp [rotationVector,PiLp.single_apply,polynomialEvaluation,polynomialRotation,
    sub_mul,ite_mul,Finset.sum_sub_distrib,euclideanCoordinates]

lemma angularCasimir_polynomialEvaluation (p : MvPolynomial (Fin n) ℝ) :
    angularCasimir (polynomialEvaluation p) = polynomialEvaluation (polynomialCasimir p) := by
  funext x
  simp only [angularCasimir,sphereRotationDerivative_polynomialEvaluation]
  simp [polynomialCasimir,polynomialEvaluation]

lemma smoothSphereLift_polynomialEvaluation (p : MvPolynomial (Fin n) ℝ) :
    smoothSphereLift (polynomialEvaluation p) (contDiff_polynomialEvaluation p) = polynomialSphereL2 p := by
  change (ContinuousMap.toLp 2 (unitSphereProbability n) ℝ) _ =
    (ContinuousMap.toLp 2 (unitSphereProbability n) ℝ) _
  congr 1

lemma shiftedAngularCasimir_polynomialEvaluation_harmonic (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p ∈ harmonicHomogeneous n k) :
    shiftedAngularCasimir (polynomialEvaluation p) =
      fun x => (1 + (k : ℝ) * ((k : ℝ) + n - 2))*polynomialEvaluation p x := by
  funext x
  rw [shiftedAngularCasimir,angularCasimir_polynomialEvaluation,
    polynomialCasimir_harmonic k p hp]
  simp only [polynomialEvaluation,map_mul,eval_C]
  ring

lemma harmonicProjection_inner (k : ℕ) (u : SphereL2 n) (v : harmonicSphereSubspace n k) :
    ⟪harmonicProjection k u, v⟫_ℝ = ⟪u, (v : SphereL2 n)⟫_ℝ := by
  rw [← sphereHarmonicDecomposition_apply,
    ← sphereHarmonicDecomposition.inner_map_map u (v : SphereL2 n),
    sphereHarmonicDecomposition_subtype, lp.inner_single_right]

 
theorem harmonicProjection_shiftedAngularCasimir (k : ℕ) (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    harmonicProjection k
      (smoothSphereLift (shiftedAngularCasimir F) (contDiff_shiftedAngularCasimir F hF)) =
        (1 + (k : ℝ) * ((k : ℝ) + n - 2)) • harmonicProjection k (smoothSphereLift F hF) := by
  apply ext_inner_right ℝ
  intro v
  rcases Submodule.mem_map.mp v.property with ⟨p,hp,hpv⟩
  have hv : (v : SphereL2 n) = polynomialSphereL2 p := hpv.symm
  rw [real_inner_smul_left (harmonicProjection k (smoothSphereLift F hF)) v
    (1 + (k : ℝ) * ((k : ℝ) + n - 2)),harmonicProjection_inner,harmonicProjection_inner,hv,
    ← smoothSphereLift_polynomialEvaluation,
    inner_shiftedAngularCasimir_symmetric]
  have he : smoothSphereLift (shiftedAngularCasimir (polynomialEvaluation p))
      (contDiff_shiftedAngularCasimir _ (contDiff_polynomialEvaluation p)) =
        (1 + (k : ℝ) * ((k : ℝ) + n - 2)) • smoothSphereLift (polynomialEvaluation p)
          (contDiff_polynomialEvaluation p) := by
    unfold smoothSphereLift
    rw [← map_smul]
    congr 1
    ext u
    exact congrFun (shiftedAngularCasimir_polynomialEvaluation_harmonic k p hp) u.val
  rw [he,real_inner_smul_right]

lemma harmonicProjection_shiftedAngularCasimirIterate (m k : ℕ) (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    harmonicProjection k
      (smoothSphereLift (shiftedAngularCasimirIterate m F)
        (contDiff_shiftedAngularCasimirIterate m F hF)) =
      (1 + (k : ℝ) * ((k : ℝ) + n - 2))^m • harmonicProjection k (smoothSphereLift F hF) := by
  induction m with
  | zero => simp [shiftedAngularCasimirIterate]
  | succ m hm =>
      change harmonicProjection k
        (smoothSphereLift (shiftedAngularCasimir (shiftedAngularCasimirIterate m F))
          (contDiff_shiftedAngularCasimir _ (contDiff_shiftedAngularCasimirIterate m F hF))) = _
      rw [harmonicProjection_shiftedAngularCasimir k _
        (contDiff_shiftedAngularCasimirIterate m F hF),hm,smul_smul,pow_succ]
      congr 1
      ring

 
theorem hasSum_smooth_shiftedAngularCasimir (hn : 3 ≤ n) (m : ℕ)
    (F : X n → ℝ) (hF : ContDiff ℝ ∞ F) :
    HasSum (fun k : ℕ => (1 + (k : ℝ) * ((k : ℝ) + n - 2))^(2*m) *
      ‖harmonicProjection k (smoothSphereLift F hF)‖^2)
      (‖smoothSphereLift (shiftedAngularCasimirIterate m F)
        (contDiff_shiftedAngularCasimirIterate m F hF)‖^2) := by
  have h := lp.hasSum_norm (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
    (sphereHarmonicDecomposition
      (smoothSphereLift (shiftedAngularCasimirIterate m F)
        (contDiff_shiftedAngularCasimirIterate m F hF)))
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,LinearIsometryEquiv.norm_map] at h
  refine h.congr_fun (fun k => ?_)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hkn : 0 ≤ (k : ℝ) + n - 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hweight : 0 ≤ 1 + (k : ℝ) * ((k : ℝ) + n - 2) :=
    add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg k) hkn)
  rw [sphereHarmonicDecomposition_apply, harmonicProjection_shiftedAngularCasimirIterate m k F hF,
    norm_smul,Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hweight _),mul_pow]
  simp only [← pow_mul,Nat.mul_comm]

 
lemma angular_weight_le_shiftedCasimir (hn : 3 ≤ n) (m q k : ℕ) (hq : q ≤ 4*m) :
    (1+(k:ℝ))^q ≤ (2:ℝ)^(2*m) * (1 + (k : ℝ) * ((k : ℝ) + n - 2))^(2*m) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfactor := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (sub_nonneg.mpr hn')
  have ha : (1+(k:ℝ))^2 ≤ 2*(1 + (k : ℝ) * ((k : ℝ) + n - 2)) := by
    nlinarith [sq_nonneg (k:ℝ)]
  calc
    (1+(k:ℝ))^q ≤ (1+(k:ℝ))^(4*m) :=
      pow_le_pow_right₀ (by nlinarith [Nat.cast_nonneg (α := ℝ) k]) hq
    _ = ((1+(k:ℝ))^2)^(2*m) := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ (2*(1 + (k : ℝ) * ((k : ℝ) + n - 2)))^(2*m) :=
      pow_le_pow_left₀ (by positivity) ha _
    _ = _ := by rw [mul_pow]

 
theorem summable_smooth_angular_weight (hn : 3 ≤ n) (m q : ℕ) (hq : q ≤ 4*m)
    (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    Summable (fun k : ℕ => (1+(k:ℝ))^q *
      ‖harmonicProjection k (smoothSphereLift F hF)‖^2) := by
  have hs := (hasSum_smooth_shiftedAngularCasimir hn m F hF).summable.mul_left
    ((2:ℝ)^(2*m))
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hs
  intro k
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (angular_weight_le_shiftedCasimir hn m q k hq)
    (sq_nonneg ‖harmonicProjection k (smoothSphereLift F hF)‖)

theorem summable_smooth_angular_weight_all (hn : 3 ≤ n) (q : ℕ) (F : (CalderonN.X n) → ℝ) (hF : ContDiff ℝ ∞ F) :
    Summable (fun k : ℕ => (1+(k:ℝ))^q *
      ‖harmonicProjection k (smoothSphereLift F hF)‖^2) :=
  summable_smooth_angular_weight hn q q (by omega) F hF

end CalderonN
