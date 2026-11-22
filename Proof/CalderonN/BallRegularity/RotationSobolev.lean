module

public import Proof.CalderonN.BallRegularity.FixedRegularity
public import Proof.CalderonN.BallRegularity.FixedCalculus
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Proof.CalderonN.SmoothSphereRotation
import Mathlib.Tactic
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.CompactSupport

/-! From Proof/Archive/CollaboratorRotationSobolevOct17.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

noncomputable section
open MeasureTheory TopologicalSpace
namespace CalderonN.BallRotation

variable {dim : ℕ} [NeZero dim]
open TauCeti OAI.AnisotropicCalderon.SmoothSphereRotation


def rotFun (j k : Fin dim) (θ : ℝ) (x : (X dim)) : (X dim) :=
  x + (Real.cos θ - 1) • (x j • EuclideanSpace.single j (1:ℝ) + x k • EuclideanSpace.single k (1:ℝ))
    + Real.sin θ • (x j • EuclideanSpace.single k (1:ℝ) - x k • EuclideanSpace.single j (1:ℝ))

theorem rotFun_apply (j k : Fin dim) (θ : ℝ) (x : (X dim)) (m : Fin dim) :
    rotFun j k θ x m = x m + (Real.cos θ - 1) * (x j * (if m = j then 1 else 0) +
      x k * (if m = k then 1 else 0)) + Real.sin θ * (x j * (if m = k then 1 else 0) -
      x k * (if m = j then 1 else 0)) := by
  simp only [rotFun, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, EuclideanSpace.single,
    PiLp.single_apply, smul_eq_mul]


def rotLin (j k : Fin dim) (θ : ℝ) : (X dim) →ₗ[ℝ] (X dim) where
  toFun := rotFun j k θ
  map_add' x y := by ext m; simp only [rotFun_apply, PiLp.add_apply]; ring
  map_smul' c x := by
    ext m
    simp only [rotFun_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem norm_rotFun (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (x : (X dim)) : ‖rotFun j k θ x‖ = ‖x‖ := by
  rw [show rotFun j k θ x = coordinateRotation j k θ x by
    ext m
    by_cases hmj : m = j
    · subst m
      simp [rotFun_apply, coordinateRotation, hjk]
      ring
    by_cases hmk : m = k
    · subst m
      simp [rotFun_apply, coordinateRotation, hjk, hjk.symm]
      ring
    simp [rotFun_apply, coordinateRotation, hjk, hmj, hmk]]
  exact coordinateRotation_norm j k θ x

def rot (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) : (X dim) ≃ₗᵢ[ℝ] (X dim) :=
  LinearIsometry.toLinearIsometryEquiv ⟨rotLin j k θ, norm_rotFun j k hjk θ⟩ rfl

theorem rot_apply_eq (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (x : (X dim)) :
    rot j k hjk θ x = rotFun j k θ x := rfl

theorem rot_apply_j (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (x : (X dim)) :
    rot j k hjk θ x j = Real.cos θ * x j - Real.sin θ * x k := by
  simp [rot_apply_eq, rotFun_apply, hjk]; ring

theorem rot_apply_k (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (x : (X dim)) :
    rot j k hjk θ x k = Real.sin θ * x j + Real.cos θ * x k := by
  simp [rot_apply_eq, rotFun_apply, hjk.symm]; ring

theorem rot_apply_other (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (x : (X dim)) (m : Fin dim)
    (hmj : m ≠ j) (hmk : m ≠ k) : rot j k hjk θ x m = x m := by
  simp [rot_apply_eq, rotFun_apply, hmj, hmk]

theorem rot_add (j k : Fin dim) (hjk : j ≠ k) (θ φ : ℝ) (x : (X dim)) :
    rot j k hjk θ (rot j k hjk φ x) = rot j k hjk (θ + φ) x := by
  ext m
  by_cases hmj : m = j
  · subst hmj; simp only [rot_apply_j, rot_apply_k, Real.cos_add, Real.sin_add]; ring
  by_cases hmk : m = k
  · subst hmk; simp only [rot_apply_j, rot_apply_k, Real.cos_add, Real.sin_add]; ring
  simp only [rot_apply_other j k hjk _ _ m hmj hmk]

theorem rot_zero (j k : Fin dim) (hjk : j ≠ k) (x : (X dim)) : rot j k hjk 0 x = x := by
  ext m; simp [rot_apply_eq, rotFun_apply]

theorem rot_symm (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) :
    (rot j k hjk θ).symm = rot j k hjk (-θ) := by
  ext1 x
  rw [LinearIsometryEquiv.symm_apply_eq, rot_add, add_neg_cancel, rot_zero]


def gen (j k : Fin dim) (x : (X dim)) : (X dim) :=
  x j • EuclideanSpace.single k 1 - x k • EuclideanSpace.single j 1

theorem hasDerivAt_rot (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (x : (X dim)) :
    HasDerivAt (fun t => rot j k hjk t x) (gen j k (rot j k hjk θ x)) θ := by
  have h := ((((Real.hasDerivAt_cos θ).sub_const 1).smul_const
    (x j • EuclideanSpace.single j (1:ℝ) + x k • EuclideanSpace.single k (1:ℝ))).const_add x).add
    ((Real.hasDerivAt_sin θ).smul_const
      (x j • EuclideanSpace.single k (1:ℝ) - x k • EuclideanSpace.single j (1:ℝ)))
  refine h.congr_deriv ?_
  ext m
  simp only [gen, rot_apply_j, rot_apply_k, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
    EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]
  split_ifs <;> simp_all <;> ring


theorem measurePreserving_rot (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) :
    MeasurePreserving (rot j k hjk θ) (volume : Measure (X dim)) volume :=
  LinearIsometryEquiv.measurePreserving _

theorem rot_mem_ball_iff (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (x : (X dim)) :
    rot j k hjk θ x ∈ ((fixedBallOpens dim) : Set (X dim)) ↔ x ∈ ((fixedBallOpens dim) : Set (X dim)) := by
  change dist (rot j k hjk θ x) 0 < 1 ↔ dist x 0 < 1
  simp

theorem preimage_rot_ball (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) :
    rot j k hjk θ ⁻¹' ((fixedBallOpens dim) : Set (X dim)) = (fixedBallOpens dim) := by
  ext x; exact rot_mem_ball_iff j k hjk θ x

theorem measurePreserving_rot_ball (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) :
    MeasurePreserving (rot j k hjk θ) ((volume : Measure (X dim)).restrict (fixedBallOpens dim))
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) := by
  have h := (measurePreserving_rot j k hjk θ).restrict_preimage (s := ((fixedBallOpens dim) : Set (X dim)))
    (fixedBallOpens dim).isOpen.measurableSet
  rwa [preimage_rot_ball] at h


theorem setIntegral_ball_comp_rot {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (g : (X dim) → F) :
    ∫ x in ((fixedBallOpens dim) : Set (X dim)), g (rot j k hjk θ x) = ∫ x in ((fixedBallOpens dim) : Set (X dim)), g x :=
  (measurePreserving_rot_ball j k hjk θ).integral_comp
    (rot j k hjk θ).toHomeomorph.measurableEmbedding g


open scoped Distributions InnerProductSpace


def compTestFunction (L : (X dim) ≃ₗᵢ[ℝ] (X dim))
    (hL : ∀ x, L x ∈ ((fixedBallOpens dim) : Set (X dim)) ↔ x ∈ ((fixedBallOpens dim) : Set (X dim)))
    (φ : 𝓓((fixedBallOpens dim), ℝ)) : 𝓓((fixedBallOpens dim), ℝ) :=
  ⟨fun x => φ (L x), φ.contDiff.comp L.contDiff,
    φ.hasCompactSupport.comp_homeomorph L.toHomeomorph,
    by
      intro x hx
      have : x ∈ tsupport ((φ : (X dim) → ℝ) ∘ (L.toHomeomorph : (X dim) → (X dim))) := hx
      rw [tsupport_comp_eq_preimage] at this
      exact (hL x).1 (φ.tsupport_subset this)⟩

@[simp]
theorem compTestFunction_apply (L : (X dim) ≃ₗᵢ[ℝ] (X dim))
    (hL : ∀ x, L x ∈ ((fixedBallOpens dim) : Set (X dim)) ↔ x ∈ ((fixedBallOpens dim) : Set (X dim)))
    (φ : 𝓓((fixedBallOpens dim), ℝ)) (x : (X dim)) : compTestFunction L hL φ x = φ (L x) := rfl

theorem symm_mem_ball_iff (L : (X dim) ≃ₗᵢ[ℝ] (X dim))
    (hL : ∀ x, L x ∈ ((fixedBallOpens dim) : Set (X dim)) ↔ x ∈ ((fixedBallOpens dim) : Set (X dim))) :
    ∀ x, L.symm x ∈ ((fixedBallOpens dim) : Set (X dim)) ↔ x ∈ ((fixedBallOpens dim) : Set (X dim)) := by
  intro x
  rw [← hL (L.symm x), L.apply_symm_apply]

theorem locallyIntegrableOn_comp_isometry {F : Type*} [NormedAddCommGroup F] {f : (X dim) → F}
    (L : (X dim) ≃ₗᵢ[ℝ] (X dim)) (hL : ∀ x, L x ∈ ((fixedBallOpens dim) : Set (X dim)) ↔ x ∈ ((fixedBallOpens dim) : Set (X dim)))
    (hf : LocallyIntegrableOn f (fixedBallOpens dim) volume) :
    LocallyIntegrableOn (fun x => f (L x)) (fixedBallOpens dim) volume := by
  rw [locallyIntegrableOn_iff (fixedBallOpens dim).isOpen.isLocallyClosed] at hf ⊢
  intro K hK hKc
  have h1 : L ⁻¹' (L '' K) = K := Set.preimage_image_eq K L.injective
  have h2 := (L.measurePreserving).integrableOn_comp_preimage
    L.toHomeomorph.measurableEmbedding (f := f) (s := L '' K)
  rw [h1] at h2
  refine h2.2 (hf _ ?_ (hKc.image L.continuous))
  rintro _ ⟨x, hx, rfl⟩
  exact (hL x).2 (hK hx)

theorem hasWeakLineDerivOn_comp_isometry {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u u' : (X dim) → F} {v : (X dim)} (L : (X dim) ≃ₗᵢ[ℝ] (X dim))
    (hL : ∀ x, L x ∈ ((fixedBallOpens dim) : Set (X dim)) ↔ x ∈ ((fixedBallOpens dim) : Set (X dim)))
    (hu : HasWeakLineDerivOn volume (fixedBallOpens dim) u u' (L v)) :
    HasWeakLineDerivOn volume (fixedBallOpens dim) (fun x => u (L x)) (fun x => u' (L x)) v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨hu.completeSpace, locallyIntegrableOn_comp_isometry L hL hu.locallyIntegrableOn,
    locallyIntegrableOn_comp_isometry L hL hu.locallyIntegrableOn_deriv, fun φ => ?_⟩
  let ψ := compTestFunction L.symm (symm_mem_ball_iff L hL) φ
  have hleft : (∫ x, lineDeriv ℝ (φ : (X dim) → ℝ) x v • u (L x)) =
      ∫ y, lineDeriv ℝ (ψ : (X dim) → ℝ) y (L v) • u y := by
    conv_rhs => rw [← (L.measurePreserving).integral_comp L.toHomeomorph.measurableEmbedding]
    congr 1; funext x; congr 1
    simp only [lineDeriv, ψ, compTestFunction_apply, map_add, map_smul,
      LinearIsometryEquiv.symm_apply_apply]
  have hright : (∫ x, (φ : (X dim) → ℝ) x • u' (L x)) = ∫ y, (ψ : (X dim) → ℝ) y • u' y := by
    conv_rhs => rw [← (L.measurePreserving).integral_comp L.toHomeomorph.measurableEmbedding]
    congr 1; funext x
    simp only [ψ, compTestFunction_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [hleft, hright]
  exact hu.integral_lineDeriv_smul_eq_neg_integral_smul ψ

theorem hasWeakFDerivOn_comp_isometry {u : (X dim) → ℝ} {g : (X dim) → (X dim)} (L : (X dim) ≃ₗᵢ[ℝ] (X dim))
    (hL : ∀ x, L x ∈ ((fixedBallOpens dim) : Set (X dim)) ↔ x ∈ ((fixedBallOpens dim) : Set (X dim)))
    (hu : HasWeakFDerivOn volume (fixedBallOpens dim) u (fun x => innerSL ℝ (g x))) :
    HasWeakFDerivOn volume (fixedBallOpens dim) (fun x => u (L x))
      (fun x => innerSL ℝ (L.symm (g (L x)))) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  have h := hasWeakLineDerivOn_comp_isometry L hL ((hasWeakFDerivOn_iff.1 hu) (L v))
  have heq : (fun x => innerSL ℝ (L.symm (g (L x))) v) =
      fun x => innerSL ℝ (g (L x)) (L v) := by
    funext x
    simp only [innerSL_apply_apply]
    rw [← L.inner_map_map, L.apply_symm_apply]
  rw [heq]
  exact h

def rotValueL (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) :
    Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) →L[ℝ]
      Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (rot j k hjk θ)
    (measurePreserving_rot_ball j k hjk θ)).toContinuousLinearMap


def rotGradL (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) :
    Lp (X dim) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) →L[ℝ]
      Lp (X dim) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
  (((rot j k hjk θ).symm.toContinuousLinearEquiv : (X dim) →L[ℝ] (X dim)).compLpL 2
    ((volume : Measure (X dim)).restrict (fixedBallOpens dim))).comp
    (Lp.compMeasurePreservingₗᵢ ℝ (rot j k hjk θ)
      (measurePreserving_rot_ball j k hjk θ)).toContinuousLinearMap

theorem rotValueL_ae (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (f : Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))) :
    ⇑(rotValueL j k hjk θ f) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => f (rot j k hjk θ x) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem rotGradL_ae (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (f : Lp (X dim) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))) :
    ⇑(rotGradL j k hjk θ f) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => (rot j k hjk θ).symm (f (rot j k hjk θ x)) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2)
      (((rot j k hjk θ).symm.toContinuousLinearEquiv : (X dim) →L[ℝ] (X dim)))
      (Lp.compMeasurePreservingₗᵢ ℝ (rot j k hjk θ) (measurePreserving_rot_ball j k hjk θ) f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_rot_ball j k hjk θ)] with x h1 h2
  simp only [rotGradL, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [h1]
  simp only [Lp.compMeasurePreservingₗᵢ_apply] at h2 ⊢
  rw [h2]
  rfl

theorem norm_rotGradL (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (f : Lp (X dim) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))) :
    ‖rotGradL j k hjk θ f‖ = ‖f‖ := by
  rw [← Lp.norm_compMeasurePreserving f (measurePreserving_rot_ball j k hjk θ),
    Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [rotGradL_ae j k hjk θ f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_rot_ball j k hjk θ)] with x h1 h2
  rw [h1, h2, LinearIsometryEquiv.norm_map]
  rfl

theorem hasWeakFDerivOn_rotate (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    HasWeakFDerivOn volume (fixedBallOpens dim) (rotValueL j k hjk θ (W1p.value u))
      (fun x => innerSL ℝ (rotGradL j k hjk θ (W1p.gradient u) x)) := by
  have h := hasWeakFDerivOn_comp_isometry (rot j k hjk θ) (rot_mem_ball_iff j k hjk θ)
    (W1p.hasWeakFDerivOn u)
  refine (h.congr_ae (rotValueL_ae j k hjk θ _).symm).congr_ae_deriv ?_
  filter_upwards [rotGradL_ae j k hjk θ (W1p.gradient u)] with x hx
  rw [hx]


def rotateFun (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2 :=
  W1p.mk (rotValueL j k hjk θ (W1p.value u)) (rotGradL j k hjk θ (W1p.gradient u))
    (hasWeakFDerivOn_rotate j k hjk θ u)

theorem value_rotateFun (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    W1p.value (rotateFun j k hjk θ u) = rotValueL j k hjk θ (W1p.value u) := W1p.value_mk _ _ _

theorem gradient_rotateFun (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    W1p.gradient (rotateFun j k hjk θ u) = rotGradL j k hjk θ (W1p.gradient u) :=
  W1p.gradient_mk _ _ _

theorem norm_rotateFun (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) : ‖rotateFun j k hjk θ u‖ = ‖u‖ := by
  have h1 := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq (rotateFun j k hjk θ u)
  have h2 := W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq u
  rw [value_rotateFun, gradient_rotateFun, norm_rotGradL] at h1
  have h3 : ‖rotValueL j k hjk θ (W1p.value u)‖ = ‖W1p.value u‖ :=
    Lp.norm_compMeasurePreserving _ _
  rw [h3, ← h2] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

end CalderonN.BallRotation

namespace CalderonN.BallRotation.W1p

variable {dim : ℕ} [NeZero dim]
open TauCeti OAI.AnisotropicCalderon.SmoothSphereRotation
open scoped Distributions InnerProductSpace

theorem value_add (u v : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    W1p.value (u + v) = W1p.value u + W1p.value v := map_add W1p.valueL u v

theorem gradient_add (u v : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    W1p.gradient (u + v) = W1p.gradient u + W1p.gradient v := map_add W1p.gradientL u v

theorem value_smul (c : ℝ) (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    W1p.value (c • u) = c • W1p.value u := map_smul W1p.valueL c u

theorem gradient_smul (c : ℝ) (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    W1p.gradient (c • u) = c • W1p.gradient u := map_smul W1p.gradientL c u

end CalderonN.BallRotation.W1p

namespace CalderonN.BallRotation

variable {dim : ℕ} [NeZero dim]
open TauCeti OAI.AnisotropicCalderon.SmoothSphereRotation
open scoped Distributions InnerProductSpace

theorem rotateFun_add (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u v : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    rotateFun j k hjk θ (u + v) = rotateFun j k hjk θ u + rotateFun j k hjk θ v := by
  apply TauCeti.W1p.ext_value
  rw [value_rotateFun, W1p.value_add, map_add, W1p.value_add, value_rotateFun, value_rotateFun]

theorem rotateFun_smul (j k : Fin dim) (hjk : j ≠ k) (θ c : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    rotateFun j k hjk θ (c • u) = c • rotateFun j k hjk θ u := by
  apply TauCeti.W1p.ext_value
  rw [W1p.value_smul, value_rotateFun, value_rotateFun, W1p.value_smul, map_smul]


def rotateₗ (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) :
    W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2 →ₗ[ℝ] W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2 where
  toFun := rotateFun j k hjk θ
  map_add' u v := rotateFun_add j k hjk θ u v
  map_smul' c u := by
    simpa only [RingHom.id_apply] using rotateFun_smul j k hjk θ c u


def rotate (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) :
    W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2 →L[ℝ] W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2 :=
  (rotateₗ j k hjk θ).mkContinuous 1 fun u => by
    simp only [one_mul]
    exact (norm_rotateFun j k hjk θ u).le

theorem rotate_apply (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) : rotate j k hjk θ u = rotateFun j k hjk θ u :=
  rfl

theorem value_rotate_ae (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    ⇑(W1p.value (rotate j k hjk θ u)) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => W1p.value u (rot j k hjk θ x) := by
  rw [rotate_apply, value_rotateFun]
  exact rotValueL_ae j k hjk θ _

theorem gradient_rotate_ae (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    ⇑(W1p.gradient (rotate j k hjk θ u)) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => (rot j k hjk θ).symm (W1p.gradient u (rot j k hjk θ x)) := by
  rw [rotate_apply, gradient_rotateFun]
  exact rotGradL_ae j k hjk θ _

theorem norm_rotate (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    (u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) : ‖rotate j k hjk θ u‖ = ‖u‖ :=
  norm_rotateFun j k hjk θ u

open scoped Gradient

theorem norm_gen_le (j k : Fin dim) (hjk : j ≠ k) (y : (X dim)) : ‖gen j k y‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hgen (i : Fin dim) :
      (gen j k y i)^2 = (if i = j then (y k)^2 else 0) + (if i = k then (y j)^2 else 0) := by
    by_cases hj : i = j
    · subst i
      simp [gen, EuclideanSpace.single, PiLp.single_apply, hjk, hjk.symm]
    by_cases hk : i = k
    · subst i
      simp [gen, EuclideanSpace.single, PiLp.single_apply, hjk, hjk.symm]
    simp [gen, EuclideanSpace.single, PiLp.single_apply, hj, hk]
  simp only [hgen]
  calc
    _ = ∑ i ∈ ({j,k} : Finset (Fin dim)), (y i)^2 := by
      simp [Finset.sum_add_distrib, Finset.sum_ite_eq', hjk, hjk.symm, add_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg (y i))

theorem rot_apply_formula (j k : Fin dim) (hjk : j ≠ k) (t : ℝ) (x : (X dim)) :
    rot j k hjk t x = x + (Real.cos t - 1) • (x j • EuclideanSpace.single j (1:ℝ) +
      x k • EuclideanSpace.single k (1:ℝ)) + Real.sin t • (x j • EuclideanSpace.single k (1:ℝ) -
      x k • EuclideanSpace.single j (1:ℝ)) := rfl

theorem continuous_rot_uncurry (j k : Fin dim) (hjk : j ≠ k) :
    Continuous fun z : (X dim) × ℝ => rot j k hjk z.2 z.1 := by
  simp only [rot_apply_formula]
  fun_prop

theorem contDiff_rot_apply (j k : Fin dim) (hjk : j ≠ k) (x : (X dim)) :
    ContDiff ℝ 1 fun t : ℝ => rot j k hjk t x := by
  simp only [rot_apply_formula]
  fun_prop

theorem norm_fderiv_apply_gen_le (j k : Fin dim) (hjk : j ≠ k) (φ : 𝓓((fixedBallOpens dim), ℝ)) (y : (X dim)) :
    ‖fderiv ℝ (φ : (X dim) → ℝ) y (gen j k y)‖ ≤ ‖∇ (φ : (X dim) → ℝ) y‖ := by
  rw [norm_gradient_eq_norm_fderiv]
  by_cases hy : y ∈ ((fixedBallOpens dim) : Set (X dim))
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have h1 : ‖gen j k y‖ ≤ 1 := by
      refine (norm_gen_le j k hjk y).trans ?_
      have : y ∈ Metric.ball (0 : (X dim)) 1 := hy
      rw [Metric.mem_ball, dist_zero_right] at this
      exact this.le
    calc ‖fderiv ℝ (φ : (X dim) → ℝ) y‖ * ‖gen j k y‖ ≤ ‖fderiv ℝ (φ : (X dim) → ℝ) y‖ * 1 := by gcongr
      _ = _ := mul_one _
  · have : fderiv ℝ (φ : (X dim) → ℝ) y = 0 :=
      fderiv_of_notMem_tsupport ℝ fun h => hy (φ.tsupport_subset h)
    simp [this]

theorem enorm_rot_sub_le (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (φ : 𝓓((fixedBallOpens dim), ℝ)) (x : (X dim)) :
    ‖φ (rot j k hjk θ x) - φ x‖ₑ ≤
      ∫⁻ t in Set.uIcc 0 θ, ‖∇ (φ : (X dim) → ℝ) (rot j k hjk t x)‖ₑ := by
  set f : ℝ → ℝ := fun t => φ (rot j k hjk t x) with hf
  have hC : ContDiff ℝ 1 f := (φ.contDiff.of_le (by simp)).comp (contDiff_rot_apply j k hjk x)
  have hderiv : ∀ t, deriv f t = fderiv ℝ (φ : (X dim) → ℝ) (rot j k hjk t x)
      (gen j k (rot j k hjk t x)) := by
    intro t
    exact (((φ.contDiff.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_rot j k hjk t x)).deriv
  have hmono : ∫⁻ t in Set.uIcc 0 θ, ‖deriv f t‖ₑ ≤
      ∫⁻ t in Set.uIcc 0 θ, ‖∇ (φ : (X dim) → ℝ) (rot j k hjk t x)‖ₑ := by
    refine lintegral_mono fun t => ?_
    rw [hderiv t]
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_fderiv_apply_gen_le j k hjk φ _)
  have hf0 : f 0 = φ x := by simp only [hf, rot_zero]
  refine le_trans ?_ hmono
  rcases le_total 0 θ with h | h
  · have := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hC.contDiffOn h
    rwa [hf0, ← Set.uIcc_of_le h] at this
  · have := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hC.contDiffOn h
    rwa [hf0, ← Set.uIcc_of_ge h, enorm_sub_rev] at this


open scoped ENNReal in
theorem lintegral_rot_sub_sq_le (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), ‖φ (rot j k hjk θ x) - φ x‖ₑ ^ (2:ℝ) ≤
      volume (Set.uIcc 0 θ) ^ (2:ℝ) *
        ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), ‖∇ (φ : (X dim) → ℝ) x‖ₑ ^ (2:ℝ) := by
  set S := Set.uIcc (0:ℝ) θ with hS
  set G : (X dim) → ℝ≥0∞ := fun y => ‖∇ (φ : (X dim) → ℝ) y‖ₑ ^ (2:ℝ) with hG
  have hGc : Continuous G :=
    (ENNReal.continuous_rpow_const).comp (continuous_gradient_testFunction φ).enorm
  have hSfin : volume S ≠ ∞ := by rw [hS, Real.volume_interval]; exact ENNReal.ofReal_ne_top
  have hpt : ∀ x, ‖φ (rot j k hjk θ x) - φ x‖ₑ ^ (2:ℝ) ≤
      volume S * ∫⁻ t in S, G (rot j k hjk t x) := by
    intro x
    have hmeas : AEMeasurable (fun t => ‖∇ (φ : (X dim) → ℝ) (rot j k hjk t x)‖ₑ)
        (volume.restrict S) :=
      ((continuous_gradient_testFunction φ).enorm.comp ((continuous_rot_uncurry j k hjk).comp
        (Continuous.prodMk continuous_const continuous_id))).aemeasurable
    have h2 := TauCeti.rpow_lintegral_le_measure_univ_rpow_mul hmeas (r := 2) one_le_two
    rw [Measure.restrict_apply_univ] at h2
    rw [show (2:ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h2
    calc ‖φ (rot j k hjk θ x) - φ x‖ₑ ^ (2:ℝ)
        ≤ (∫⁻ t in S, ‖∇ (φ : (X dim) → ℝ) (rot j k hjk t x)‖ₑ) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow (enorm_rot_sub_le j k hjk θ φ x) (by norm_num)
      _ ≤ _ := h2
  have hjoint : AEMeasurable (Function.uncurry fun x t => G (rot j k hjk t x))
      (((volume : Measure (X dim)).restrict (fixedBallOpens dim)).prod (volume.restrict S)) :=
    (hGc.comp (continuous_rot_uncurry j k hjk)).measurable.aemeasurable
  calc ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), ‖φ (rot j k hjk θ x) - φ x‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), volume S * ∫⁻ t in S, G (rot j k hjk t x) :=
        lintegral_mono hpt
    _ = volume S * ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), ∫⁻ t in S, G (rot j k hjk t x) :=
        lintegral_const_mul' _ _ hSfin
    _ = volume S * ∫⁻ t in S, ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), G (rot j k hjk t x) := by
        rw [lintegral_lintegral_swap hjoint]
    _ = volume S * ∫⁻ t in S, ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), G x := by
        congr 1
        exact lintegral_congr fun t =>
          (measurePreserving_rot_ball j k hjk t).lintegral_comp hGc.measurable
    _ = volume S ^ (2:ℝ) * ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), G x := by
        rw [lintegral_const, Measure.restrict_apply_univ, ENNReal.rpow_two]
        ring

theorem eLpNorm_rot_sub_le (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    eLpNorm (fun x => φ (rot j k hjk θ x) - φ x) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) ≤
      ENNReal.ofReal |θ| *
        eLpNorm (fun x => ∇ (φ : (X dim) → ℝ) x) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) := by
  have h1 : AEStronglyMeasurable (fun x => φ (rot j k hjk θ x) - φ x)
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
    ((φ.continuous.comp (rot j k hjk θ).continuous).sub φ.continuous).aestronglyMeasurable
  have h2 : AEStronglyMeasurable (fun x => ∇ (φ : (X dim) → ℝ) x)
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
    (continuous_gradient_testFunction φ).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top h1,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top h2]
  simp only [ENNReal.toReal_ofNat]
  have hvol : volume (Set.uIcc 0 θ) = ENNReal.ofReal |θ| := by
    rw [Real.volume_interval, sub_zero]
  calc (∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), ‖φ (rot j k hjk θ x) - φ x‖ₑ ^ (2:ℝ)) ^ (1 / 2 : ℝ)
      ≤ (volume (Set.uIcc 0 θ) ^ (2:ℝ) *
          ∫⁻ x in ((fixedBallOpens dim) : Set (X dim)), ‖∇ (φ : (X dim) → ℝ) x‖ₑ ^ (2:ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_rot_sub_sq_le j k hjk θ φ) (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), one_div,
          ENNReal.rpow_rpow_inv two_ne_zero, hvol]


theorem rotate_ofTestFunction (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ) (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    rotate j k hjk θ (W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ) =
      W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2
        (compTestFunction (rot j k hjk θ) (rot_mem_ball_iff j k hjk θ) φ) := by
  apply W1p.ext_value
  apply Lp.ext
  have hq := (measurePreserving_rot_ball j k hjk θ).quasiMeasurePreserving.tendsto_ae
  filter_upwards [value_rotate_ae j k hjk θ (W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ),
    hq.eventually (testFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 φ),
    testFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2
      (compTestFunction (rot j k hjk θ) (rot_mem_ball_iff j k hjk θ) φ)] with x h1 h2 h3
  rw [h1, W1p.value_ofTestFunctionₗ, W1p.value_ofTestFunctionₗ, h2, h3]
  rfl


theorem rotate_mem_w1p0Submodule (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    {u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2}
    (hu : u ∈ w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    rotate j k hjk θ u ∈ w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2 := by
  have hclosed : IsClosed ((rotate j k hjk θ) ⁻¹'
      (w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2 :
        Set (W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2))) :=
    (w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2).isClosed.preimage
      (rotate j k hjk θ).continuous
  have hsub := w1p0Submodule_subset_of_isClosed hclosed (fun φ => by
    refine Set.mem_preimage.2 (SetLike.mem_coe.2 ?_)
    rw [rotate_ofTestFunction]
    exact W1p.ofTestFunctionₗ_mem_w1p0Submodule _)
  exact SetLike.mem_coe.1 (Set.mem_preimage.1 (hsub (SetLike.mem_coe.2 hu)))


theorem norm_value_rotate_sub_le (j k : Fin dim) (hjk : j ≠ k) (θ : ℝ)
    {u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2}
    (hu : u ∈ w1p0Submodule (volume : Measure (X dim)) (fixedBallOpens dim) 2) :
    ‖W1p.value (rotate j k hjk θ u) - W1p.value u‖ ≤ |θ| * ‖W1p.gradient u‖ := by
  have hclosed : IsClosed {u : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2 |
      ‖W1p.value (rotate j k hjk θ u) - W1p.value u‖ ≤ |θ| * ‖W1p.gradient u‖} :=
    isClosed_le ((W1p.valueL.continuous.comp (rotate j k hjk θ).continuous).sub
      W1p.valueL.continuous).norm (continuous_const.mul W1p.gradientL.continuous.norm)
  refine w1p0Submodule_subset_of_isClosed hclosed (fun φ => ?_) hu
  simp only [Set.mem_ofPred_eq]
  have hq := (measurePreserving_rot_ball j k hjk θ).quasiMeasurePreserving.tendsto_ae
  have hL : ‖W1p.value (rotate j k hjk θ (W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ)) -
      W1p.value (W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ)‖ =
      (eLpNorm (fun x => φ (rot j k hjk θ x) - φ x) 2
        ((volume : Measure (X dim)).restrict (fixedBallOpens dim))).toReal := by
    rw [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_sub
        (W1p.value (rotate j k hjk θ (W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ)))
        (W1p.value (W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ)),
      value_rotate_ae j k hjk θ (W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ),
      hq.eventually (testFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 φ),
      testFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 φ] with x h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, W1p.value_ofTestFunctionₗ, h3, h4]
  have hR : ‖W1p.gradient (W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ)‖ =
      (eLpNorm (fun x => ∇ (φ : (X dim) → ℝ) x) 2
        ((volume : Measure (X dim)).restrict (fixedBallOpens dim))).toReal := by
    rw [W1p.gradient_ofTestFunctionₗ, norm_gradientTestFunctionLp]
  rw [hL, hR]
  have hfin : eLpNorm (fun x => ∇ (φ : (X dim) → ℝ) x) 2
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) ≠ ⊤ :=
    (memLp_gradient_testFunction 2 φ).eLpNorm_ne_top
  calc _ ≤ (ENNReal.ofReal |θ| * eLpNorm (fun x => ∇ (φ : (X dim) → ℝ) x) 2
        ((volume : Measure (X dim)).restrict (fixedBallOpens dim))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
          (eLpNorm_rot_sub_le j k hjk θ φ)
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg θ)]

end CalderonN.BallRotation
