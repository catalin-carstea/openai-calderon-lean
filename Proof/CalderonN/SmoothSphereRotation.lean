module

public import Proof.CalderonN.OrthogonalSphereMeasure
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

@[expose] public section

/- Adopted from the selected ZIP, lean/Calderon/SmoothSphereRotation.lean.
   Complete generic module; proof bodies preserved, local imports rewritten.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal
namespace OAI.AnisotropicCalderon.SmoothSphereRotation
open SphereHarmonic OrthogonalSphereMeasure

variable {n : ℕ}

 
def coordinateRotation (i j : Fin n) (t : ℝ) (x : (CalderonN.X n)) : (CalderonN.X n) :=
  if i = j then x else WithLp.toLp 2 fun l =>
    if l = i then Real.cos t * x i - Real.sin t * x j else
    if l = j then Real.sin t * x i + Real.cos t * x j else x l

 
def rotationVector (i j : Fin n) (x : (CalderonN.X n)) : (CalderonN.X n) :=
  x i • PiLp.single 2 j (1 : ℝ) - x j • PiLp.single 2 i (1 : ℝ)

def sphereRotationDerivative (i j : Fin n) (F : (CalderonN.X n) → ℝ) (x : (CalderonN.X n)) : ℝ :=
  fderiv ℝ F x (rotationVector i j x)

lemma rotation_pair_square (t a b : ℝ) :
    (Real.cos t * a - Real.sin t * b)^2 +
      (Real.sin t * a + Real.cos t * b)^2 = a^2 + b^2 := by
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * (a^2 + b^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

lemma rotation_inverse_first (t a b : ℝ) :
    Real.cos t * (Real.cos t * a + Real.sin t * b) -
      Real.sin t * (-Real.sin t * a + Real.cos t * b) = a := by
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * a := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

lemma rotation_inverse_second (t a b : ℝ) :
    Real.sin t * (Real.cos t * a + Real.sin t * b) +
      Real.cos t * (-Real.sin t * a + Real.cos t * b) = b := by
  calc
    _ = (Real.sin t ^ 2 + Real.cos t ^ 2) * b := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

lemma coordinateRotation_add (i j : Fin n) (t : ℝ) (x y : (CalderonN.X n)) :
    coordinateRotation i j t (x+y) = coordinateRotation i j t x +
      coordinateRotation i j t y := by
  ext l
  by_cases hij : i=j
  · simp [coordinateRotation,hij]
  · by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp [coordinateRotation,hij,Ne.symm hij,hli,hlj] <;> ring

lemma coordinateRotation_smul (i j : Fin n) (t c : ℝ) (x : (CalderonN.X n)) :
    coordinateRotation i j t (c • x) = c • coordinateRotation i j t x := by
  ext l
  by_cases hij : i=j
  · simp [coordinateRotation,hij]
  · by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp [coordinateRotation,hij,Ne.symm hij,hli,hlj] <;> ring

lemma coordinateRotation_inverse (i j : Fin n) (t : ℝ) (x : (CalderonN.X n)) :
    coordinateRotation i j t (coordinateRotation i j (-t) x) = x := by
  by_cases hij : i=j
  · simp [coordinateRotation,hij]
  · ext l
    by_cases hli : l=i
    · subst l
      simpa [coordinateRotation,hij,Ne.symm hij,Real.cos_neg,Real.sin_neg] using
        rotation_inverse_first t (x i) (x j)
    · by_cases hlj : l=j
      · subst l
        simpa [coordinateRotation,hij,Ne.symm hij,Real.cos_neg,Real.sin_neg] using
          rotation_inverse_second t (x i) (x j)
      · simp [coordinateRotation,hij,Ne.symm hij,hli,hlj]

lemma coordinateRotation_norm (i j : Fin n) (t : ℝ) (x : (CalderonN.X n)) :
    ‖coordinateRotation i j t x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  by_cases hij : i = j
  · simp [coordinateRotation, hij]
  have hi : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
  have hj : j ∈ (Finset.univ : Finset (Fin n)).erase i := by simp [Ne.symm hij]
  rw [← Finset.sum_erase_add _ _ hi, ← Finset.sum_erase_add _ _ hj]
  rw [← Finset.sum_erase_add _ _ hi, ← Finset.sum_erase_add _ _ hj]
  have hrest : (∑ l ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j,
      coordinateRotation i j t x l ^ 2) =
      ∑ l ∈ ((Finset.univ : Finset (Fin n)).erase i).erase j, x l ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    have ⟨hlj, hli, _⟩ := Finset.mem_erase.mp hl |>.imp_right Finset.mem_erase.mp
    simp [coordinateRotation, hij, hli, hlj]
  rw [hrest]
  simp only [coordinateRotation, hij, ite_false, PiLp.toLp_apply, Ne.symm hij, ite_true]
  linarith only [rotation_pair_square t (x i) (x j)]


def coordinateRotationIsometry (i j : Fin n) (t : ℝ) : (CalderonN.X n) ≃ₗᵢ[ℝ] (CalderonN.X n) where
  toFun := coordinateRotation i j t
  invFun := coordinateRotation i j (-t)
  left_inv x := by simpa using coordinateRotation_inverse i j (-t) x
  right_inv x := coordinateRotation_inverse i j t x
  map_add' := coordinateRotation_add i j t
  map_smul' c x := coordinateRotation_smul i j t c x
  norm_map' := coordinateRotation_norm i j t

lemma coordinateRotation_zero (i j : Fin n) (x : (CalderonN.X n)) :
    coordinateRotation i j 0 x = x := by
  ext l
  by_cases hij : i=j
  · simp [coordinateRotation,hij]
  · by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp [coordinateRotation,hij,Ne.symm hij,hli,hlj]

lemma rotationVector_self (i : Fin n) (x : (CalderonN.X n)) : rotationVector i i x = 0 := by
  simp [rotationVector]

lemma contDiff_coordinateRotation (i j : Fin n) :
    ContDiff ℝ ∞ (fun q : ℝ × (CalderonN.X n) => coordinateRotation i j q.1 q.2) := by
  apply contDiff_piLp'
  intro l
  by_cases hij : i=j
  · simp only [coordinateRotation,ite_eq_left hij]
    fun_prop
  · by_cases hli : l=i <;> by_cases hlj : l=j <;>
      simp only [coordinateRotation,ite_eq_right hij,Ne.symm hij,PiLp.toLp_apply,hli,hlj,ite_true,ite_false] <;> fun_prop

lemma continuous_sphereCoordinateRotation (i j : Fin n) :
    Continuous (fun q : ℝ × (UnitSphere n) => coordinateRotation i j q.1 q.2.val) := by
  have h1 : Continuous (fun q : ℝ × (CalderonN.X n) => coordinateRotation i j q.1 q.2) :=
    (contDiff_coordinateRotation i j).continuous
  have h2 : Continuous (fun q : ℝ × (UnitSphere n) => (q.1,q.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  convert! h1.comp h2 using 1

lemma contDiff_rotationVector (i j : Fin n) : ContDiff ℝ ∞ (rotationVector i j) := by
  unfold rotationVector
  fun_prop

lemma contDiff_sphereRotationDerivative (i j : Fin n) (F : (CalderonN.X n) → ℝ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (sphereRotationDerivative i j F) := by
  exact (contDiff_infty_iff_fderiv.mp hF).2.clm_apply (contDiff_rotationVector i j)

lemma hasDerivAt_coordinateRotation (i j : Fin n) (t : ℝ) (x : (CalderonN.X n)) :
    HasDerivAt (fun s => coordinateRotation i j s x)
      (rotationVector i j (coordinateRotation i j t x)) t := by
  have hpi : HasDerivAt (fun s => fun l => coordinateRotation i j s x l)
      (fun l => rotationVector i j (coordinateRotation i j t x) l) t := by
    apply hasDerivAt_pi.mpr
    intro l
    by_cases hij : i=j
    · simpa [coordinateRotation,hij,rotationVector] using hasDerivAt_const t (x l)
    · by_cases hli : l=i
      · subst l
        convert ((Real.hasDerivAt_cos t).mul_const (x i)).sub
          ((Real.hasDerivAt_sin t).mul_const (x j)) using 1 <;>
          simp [coordinateRotation,rotationVector,hij,Ne.symm hij,funext_iff,Pi.sub_apply,Pi.add_apply,mul_comm] <;> ring
      · by_cases hlj : l=j
        · subst l
          convert ((Real.hasDerivAt_sin t).mul_const (x i)).add
            ((Real.hasDerivAt_cos t).mul_const (x j)) using 1 <;>
            simp [coordinateRotation,rotationVector,hij,Ne.symm hij,funext_iff,Pi.sub_apply,Pi.add_apply,mul_comm] <;> ring
        · simpa [coordinateRotation,rotationVector,hij,Ne.symm hij,hli,hlj,Ne.symm hli,Ne.symm hlj]
            using hasDerivAt_const t (x l)
  convert!
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hpi using 1 <;> rfl

lemma hasDerivAt_rotation_comp (i j : Fin n) (F : (CalderonN.X n) → ℝ)
    (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : (CalderonN.X n)) :
    HasDerivAt (fun s => F (coordinateRotation i j s x))
      (sphereRotationDerivative i j F (coordinateRotation i j t x)) t := by
  exact ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_coordinateRotation i j t x)

variable [NeZero n]

lemma integrable_sphere_continuous (f : (UnitSphere n) → ℝ) (hf : Continuous f) :
    Integrable f (unitSphereProbability n) := by
  have hi := hf.continuousOn.integrableOn_of_subset_isCompact isCompact_univ
    MeasurableSet.univ (show (univ : Set (UnitSphere n)) ⊆ univ from Subset.rfl)
    (show (unitSphereProbability n) univ ≠ (⊤ : ℝ≥0∞) by simp)
  simpa only [IntegrableOn,Measure.restrict_univ] using hi

lemma integral_rotation_product (i j : Fin n) (t : ℝ) (F G : (CalderonN.X n) → ℝ) :
    (∫ u : (UnitSphere n), F (coordinateRotation i j t u.val) *
      G (coordinateRotation i j t u.val) ∂(unitSphereProbability n)) =
    ∫ u : (UnitSphere n), F u.val * G u.val ∂(unitSphereProbability n) := by
  exact (orthogonalSphereHomeomorph_sphereProbability_preserving
    (coordinateRotationIsometry i j t)).integral_comp
      (orthogonalSphereHomeomorph (coordinateRotationIsometry i j t)).measurableEmbedding
      (fun u : (UnitSphere n) => F u.val * G u.val)

 
lemma exists_rotation_product_derivative_bound (i j : Fin n) (F G : (CalderonN.X n) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (-1 : ℝ) 1, ∀ u : (UnitSphere n),
      ‖sphereRotationDerivative i j F (coordinateRotation i j t u.val) *
        G (coordinateRotation i j t u.val) + F (coordinateRotation i j t u.val) *
        sphereRotationDerivative i j G (coordinateRotation i j t u.val)‖ ≤ C := by
  let D : ℝ × (UnitSphere n) → ℝ := fun q =>
    sphereRotationDerivative i j F (coordinateRotation i j q.1 q.2.val) *
      G (coordinateRotation i j q.1 q.2.val) +
    F (coordinateRotation i j q.1 q.2.val) *
      sphereRotationDerivative i j G (coordinateRotation i j q.1 q.2.val)
  have hrot : Continuous (fun q : ℝ × (UnitSphere n) => coordinateRotation i j q.1 q.2.val) :=
    continuous_sphereCoordinateRotation i j
  have hD : Continuous D := by
    exact (((contDiff_sphereRotationDerivative i j F hF).continuous.comp hrot).mul
      (hG.continuous.comp hrot)).add
      ((hF.continuous.comp hrot).mul
        ((contDiff_sphereRotationDerivative i j G hG).continuous.comp hrot))
  have hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ (univ : Set (UnitSphere n))) :=
    isCompact_Icc.prod isCompact_univ
  rcases hK.bddAbove_image hD.norm.continuousOn with ⟨C,hC⟩
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro t ht u
  exact (hC (mem_image_of_mem _ (show (t,u) ∈ Icc (-1 : ℝ) 1 ×ˢ
    (univ : Set (UnitSphere n)) from ⟨ht,mem_univ _⟩))).trans (le_max_left _ _)

 
theorem integral_sphereRotationDerivative_skew (i j : Fin n) (F G : (CalderonN.X n) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (∫ u : (UnitSphere n), sphereRotationDerivative i j F u.val * G u.val ∂(unitSphereProbability n)) =
      -(∫ u : (UnitSphere n), F u.val * sphereRotationDerivative i j G u.val ∂(unitSphereProbability n)) := by
  let H : ℝ → (UnitSphere n) → ℝ := fun t u =>
    F (coordinateRotation i j t u.val) * G (coordinateRotation i j t u.val)
  let D : ℝ → (UnitSphere n) → ℝ := fun t u =>
    sphereRotationDerivative i j F (coordinateRotation i j t u.val) *
      G (coordinateRotation i j t u.val) +
    F (coordinateRotation i j t u.val) *
      sphereRotationDerivative i j G (coordinateRotation i j t u.val)
  have hrot (t : ℝ) : Continuous (fun u : (UnitSphere n) => coordinateRotation i j t u.val) :=
    (coordinateRotationIsometry i j t).continuous.comp continuous_subtype_val
  have hH (t : ℝ) : Continuous (H t) :=
    (hF.continuous.comp (hrot t)).mul (hG.continuous.comp (hrot t))
  have hD (t : ℝ) : Continuous (D t) :=
    (((contDiff_sphereRotationDerivative i j F hF).continuous.comp (hrot t)).mul
      (hG.continuous.comp (hrot t))).add
      ((hF.continuous.comp (hrot t)).mul
        ((contDiff_sphereRotationDerivative i j G hG).continuous.comp (hrot t)))
  obtain ⟨C,hC,hbound⟩ := exists_rotation_product_derivative_bound i j F G hF hG
  have hdiff : ∀ u : (UnitSphere n), ∀ t : ℝ, HasDerivAt (fun s => H s u) (D t u) t := by
    intro u t
    exact (hasDerivAt_rotation_comp i j F hF t u.val).mul
      (hasDerivAt_rotation_comp i j G hG t u.val)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := H) (F' := D) (μ := (unitSphereProbability n)) (x₀ := (0 : ℝ))
    (s := Ioo (-1 : ℝ) 1) (bound := fun _ : (UnitSphere n) => C)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hH t).aestronglyMeasurable)
    (integrable_sphere_continuous (H 0) (hH 0))
    ((hD 0).aestronglyMeasurable)
    (Eventually.of_forall fun u t ht => hbound t ⟨le_of_lt ht.1,le_of_lt ht.2⟩ u)
    (integrable_const C)
    (Eventually.of_forall fun u t _ => hdiff u t)).2
  have hconst : (fun t => ∫ u : (UnitSphere n), H t u ∂(unitSphereProbability n)) =
      fun _ : ℝ => ∫ u : (UnitSphere n), F u.val * G u.val ∂(unitSphereProbability n) := by
    funext t
    exact integral_rotation_product i j t F G
  have hz : (∫ u : (UnitSphere n), D 0 u ∂(unitSphereProbability n)) = 0 :=
    hd.unique (by
      rw [hconst]
      exact hasDerivAt_const (0 : ℝ)
        (∫ u : (UnitSphere n), F u.val * G u.val ∂(unitSphereProbability n)))
  have hleft := integrable_sphere_continuous
    (fun u : (UnitSphere n) => sphereRotationDerivative i j F u.val * G u.val)
    (((contDiff_sphereRotationDerivative i j F hF).continuous.comp continuous_subtype_val).mul
      (hG.continuous.comp continuous_subtype_val))
  have hright := integrable_sphere_continuous
    (fun u : (UnitSphere n) => F u.val * sphereRotationDerivative i j G u.val)
    ((hF.continuous.comp continuous_subtype_val).mul
      ((contDiff_sphereRotationDerivative i j G hG).continuous.comp continuous_subtype_val))
  simp only [D,coordinateRotation_zero] at hz
  rw [integral_add hleft hright] at hz
  linarith

lemma sphereRotationDerivative_eq_zero_of_sphere_zero (i j : Fin n) (F : (CalderonN.X n) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hzero : ∀ u : (UnitSphere n), F u.val = 0) (u : (UnitSphere n)) :
    sphereRotationDerivative i j F u.val = 0 := by
  have hz : (fun t : ℝ => F (coordinateRotation i j t u.val)) = fun _ : ℝ => 0 := by
    funext t
    exact hzero (orthogonalSphereHomeomorph (coordinateRotationIsometry i j t) u)
  have hd := hasDerivAt_rotation_comp i j F hF 0 u.val
  simp only [coordinateRotation_zero] at hd
  exact hd.unique (by rw [hz]; exact hasDerivAt_const (0 : ℝ) (0 : ℝ))

end OAI.AnisotropicCalderon.SmoothSphereRotation
