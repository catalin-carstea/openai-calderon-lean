module

public import Proof.CalderonN.NormalGeodesicPhase

/-! Port of the named module in the checked Proposition 5.3 release.
All variations refer to the admitted initial-velocity parameter of the same normal map. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma fderiv_coordinateGeodesicSpray (g : (MetricField dim)) (p : (X dim) × (X dim))
    (hΓ : DifferentiableAt ℝ (connectionBilinear g) p.1) (a b : (X dim)) :
    fderiv ℝ (coordinateGeodesicSpray g) p (a,b) =
      (b,-(connectionBilinear g p.1 p.2 b+
        (connectionBilinear g p.1 b p.2+fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2))) := by
  have hD := hΓ.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜:=ℝ) (p:=p))
  have hV := hasFDerivAt_snd (𝕜:=ℝ) (p:=p)
  have hR := (hD.clm_apply hV).clm_apply hV
  have hd := hV.prodMk hR.neg
  have heq : coordinateGeodesicSpray g =
      (fun q : (X dim) × (X dim) => (q.2,-connectionBilinear g q.1 q.2 q.2)) := by
    funext q
    simp only [coordinateGeodesicSpray,connectionBilinear_apply]
  simp only [Function.comp_def,Pi.neg_apply] at hd
  rw [heq,hd.fderiv]
  simp only [ContinuousLinearMap.prod_apply,_root_.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    _root_.neg_apply]
  rfl

lemma norm_bilinear_apply_le (L : (X dim) →L[ℝ] (X dim) →L[ℝ] (X dim)) (a b : (X dim)) :
    ‖L a b‖ ≤ ‖L‖*‖a‖*‖b‖ :=
  ((L a).le_opNorm b).trans (mul_le_mul_of_nonneg_right (L.le_opNorm a) (norm_nonneg b))

lemma norm_trilinear_apply_le (L : (X dim) →L[ℝ] (X dim) →L[ℝ] (X dim) →L[ℝ] (X dim)) (a b c : (X dim)) :
    ‖L a b c‖ ≤ ‖L‖*‖a‖*‖b‖*‖c‖ :=
  (norm_bilinear_apply_le (L a) b c).trans (by gcongr; exact L.le_opNorm a)

/-- Uniform first-variation coefficient budget for the coordinate geodesic spray. -/
theorem norm_fderiv_coordinateGeodesicSpray_le (g : (MetricField dim)) (p : (X dim) × (X dim))
    (hΓ : DifferentiableAt ℝ (connectionBilinear g) p.1) (C D V : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hΓ0 : ‖connectionBilinear g p.1‖ ≤ C) (hΓ1 : ‖fderiv ℝ (connectionBilinear g) p.1‖ ≤ D)
    (hSpeed : ‖p.2‖ ≤ V) :
    ‖fderiv ℝ (coordinateGeodesicSpray g) p‖ ≤ 1+2*C*V+D*V^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  rintro ⟨a,b⟩
  rw [fderiv_coordinateGeodesicSpray g p hΓ a b,Prod.norm_mk,norm_neg]
  have hb : ‖b‖ ≤ ‖((a,b):(X dim) × (X dim))‖ := norm_snd_le ((a,b):(X dim) × (X dim))
  have ha : ‖a‖ ≤ ‖((a,b):(X dim) × (X dim))‖ := norm_fst_le ((a,b):(X dim) × (X dim))
  have h1 : ‖connectionBilinear g p.1 p.2 b‖ ≤ C*V*‖b‖ :=
    (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have h2 : ‖connectionBilinear g p.1 b p.2‖ ≤ C*‖b‖*V :=
    (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have h3 : ‖fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2‖ ≤ D*‖a‖*V^2 := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2‖ ≤ D*‖a‖*V*V :=
      (norm_trilinear_apply_le _ _ _ _).trans (by gcongr)
    convert hh using 1 <;> ring
  have hsum : ‖connectionBilinear g p.1 p.2 b+
      (connectionBilinear g p.1 b p.2+fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2)‖ ≤
      (2*C*V+D*V^2)*‖((a,b):(X dim) × (X dim))‖ := by
    calc
      _ ≤ ‖connectionBilinear g p.1 p.2 b‖+
          (‖connectionBilinear g p.1 b p.2‖+‖fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ C*V*‖b‖+(C*‖b‖*V+D*‖a‖*V^2) := add_le_add h1 (add_le_add h2 h3)
      _ ≤ C*V*‖((a,b):(X dim) × (X dim))‖+(C*‖((a,b):(X dim) × (X dim))‖*V+D*‖((a,b):(X dim) × (X dim))‖*V^2) := by gcongr
      _ = _ := by ring
  have hN : 0 ≤ 2*C*V+D*V^2 := by positivity
  have hmul := mul_nonneg hN (norm_nonneg ((a,b):(X dim) × (X dim)))
  apply max_le
  · nlinarith only [hb,hmul]
  · nlinarith only [hsum,norm_nonneg ((a,b):(X dim) × (X dim))]

/-- The velocity component of the variational equation gains one small speed factor. -/
theorem norm_fderiv_coordinateGeodesicSpray_snd_le (g : (MetricField dim)) (p J : (X dim) × (X dim))
    (hΓ : DifferentiableAt ℝ (connectionBilinear g) p.1) (C D V : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hΓ0 : ‖connectionBilinear g p.1‖ ≤ C) (hΓ1 : ‖fderiv ℝ (connectionBilinear g) p.1‖ ≤ D)
    (hSpeed : ‖p.2‖ ≤ V) :
    ‖(fderiv ℝ (coordinateGeodesicSpray g) p J).2‖ ≤ (2*C*V+D*V^2)*‖J‖ := by
  rcases J with ⟨a,b⟩
  rw [fderiv_coordinateGeodesicSpray g p hΓ a b]
  change ‖-(connectionBilinear g p.1 p.2 b+
    (connectionBilinear g p.1 b p.2+fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2))‖ ≤ _
  rw [norm_neg]
  have hb : ‖b‖ ≤ ‖((a,b):(X dim) × (X dim))‖ := norm_snd_le ((a,b):(X dim) × (X dim))
  have ha : ‖a‖ ≤ ‖((a,b):(X dim) × (X dim))‖ := norm_fst_le ((a,b):(X dim) × (X dim))
  have h1 : ‖connectionBilinear g p.1 p.2 b‖ ≤ C*V*‖b‖ :=
    (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have h2 : ‖connectionBilinear g p.1 b p.2‖ ≤ C*‖b‖*V :=
    (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have h3 : ‖fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2‖ ≤ D*‖a‖*V^2 := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2‖ ≤ D*‖a‖*V*V :=
      (norm_trilinear_apply_le _ _ _ _).trans (by gcongr)
    convert hh using 1 <;> ring
  have hsum : ‖connectionBilinear g p.1 p.2 b+
      (connectionBilinear g p.1 b p.2+fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2)‖ ≤
      (2*C*V+D*V^2)*‖((a,b):(X dim) × (X dim))‖ := by
    calc
      _ ≤ ‖connectionBilinear g p.1 p.2 b‖+
          (‖connectionBilinear g p.1 b p.2‖+‖fderiv ℝ (connectionBilinear g) p.1 a p.2 p.2‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ C*V*‖b‖+(C*‖b‖*V+D*‖a‖*V^2) := add_le_add h1 (add_le_add h2 h3)
      _ ≤ C*V*‖((a,b):(X dim) × (X dim))‖+(C*‖((a,b):(X dim) × (X dim))‖*V+D*‖((a,b):(X dim) × (X dim))‖*V^2) := by gcongr
      _ = _ := by ring
  exact hsum

end CalderonN
