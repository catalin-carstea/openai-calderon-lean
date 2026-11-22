module

public import Proof.Manuscript.MovingTrace.SphericalNormalCollar
public import Proof.Manuscript.MovingTraceSymbols
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN Set Metric
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

variable {dim : ℕ} [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]

/-- The angular inverse stereographic chart viewed as an ambient unit
vector. It is the angular factor of the signed collar. -/
def angularPoint (v : ↥(sphere (0 : X dim) 1)) (x : AngularCoordinates dim) : X dim :=
  (stereographic' (dim - 1) v).symm x

def stereoRangeIsometry (v : ↥(sphere (0 : X dim) 1)) :
    (ℝ ∙ (v : X dim))ᗮ ≃ₗᵢ[ℝ] AngularCoordinates dim :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton (dim - 1) (ne_zero_of_mem_unit_sphere v)).repr

theorem angularPoint_norm (v : ↥(sphere (0 : X dim) 1)) (x : AngularCoordinates dim) :
    ‖angularPoint v x‖ = 1 :=
  norm_eq_of_mem_sphere ((stereographic' (dim - 1) v).symm x)

theorem angularPoint_contDiff (v : ↥(sphere (0 : X dim) 1)) : ContDiff ℝ ∞ (angularPoint v) := by
  change ContDiff ℝ ∞ (fun x : AngularCoordinates dim => stereoInvFunAux (v : X dim)
    (((stereoRangeIsometry v).symm x : (ℝ ∙ (v : X dim))ᗮ) : X dim))
  exact (contDiff_stereoInvFunAux (m := ∞)).comp
    ((Submodule.subtypeL (ℝ ∙ (v : X dim))ᗮ).contDiff.comp (stereoRangeIsometry v).symm.contDiff)

/-- Inverse of the angular chart on the ambient complement of its polar
denominator. Restriction to the sphere is the Mathlib stereographic chart. -/
def angularReadout (v : ↥(sphere (0 : X dim) 1)) (z : X dim) : AngularCoordinates dim :=
  stereoRangeIsometry v (stereoToFun (v : X dim) z)

theorem angularReadout_contDiffOn (v : ↥(sphere (0 : X dim) 1)) :
    ContDiffOn ℝ ∞ (angularReadout v) {z : X dim | ⟪(v : X dim),z⟫_ℝ ≠ 1} :=
  (stereoRangeIsometry v).contDiff.comp_contDiffOn (contDiffOn_stereoToFun (n := ∞))

/-- Normalized angular direction of a nonzero ambient vector. -/
def direction (z : X dim) : X dim := ‖z‖⁻¹ • z

omit [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] in
theorem direction_norm {z : X dim} (hz : z ≠ 0) : ‖direction z‖ = 1 := by
  have hn := norm_pos_iff.mpr hz
  rw [direction, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']

omit [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] in
theorem norm_contDiffOn_compl_zero :
    ContDiffOn ℝ ∞ (norm : X dim → ℝ) ({0}ᶜ : Set (X dim)) :=
  contDiffOn_id.norm ℝ (fun _ hz => hz)

omit [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] in
theorem direction_contDiffOn : ContDiffOn ℝ ∞ (direction : X dim → X dim) ({0}ᶜ : Set (X dim)) :=
  (norm_contDiffOn_compl_zero.inv (fun z hz => norm_ne_zero_iff.mpr hz)).smul contDiffOn_id

/-- The inverse signed spherical collar reads the stereographic coordinate
of the direction and the signed inward radial depth. -/
def polarReadout (v : ↥(sphere (0 : X dim) 1)) (z : X dim) : AngularCoordinates dim × ℝ :=
  (angularReadout v (direction z), 1 - ‖z‖)

def polarReadoutDomain (v : ↥(sphere (0 : X dim) 1)) : Set (X dim) :=
  {z | z ≠ 0 ∧ ⟪(v : X dim), direction z⟫_ℝ ≠ 1}

theorem polarReadoutDomain_isOpen (v : ↥(sphere (0 : X dim) 1)) : IsOpen (polarReadoutDomain v) := by
  let V : Set (X dim) := ({0}ᶜ : Set (X dim))
  let W : Set ℝ := {1}ᶜ
  have hV : IsOpen V := isOpen_compl_singleton
  have hW : IsOpen W := isOpen_compl_singleton
  have hConst : ContinuousOn (fun _ : X dim => (v : X dim)) V := continuousOn_const
  have h := (hConst.inner direction_contDiffOn.continuousOn).isOpen_inter_preimage hV hW
  exact h

theorem polarReadout_contDiffOn (v : ↥(sphere (0 : X dim) 1)) :
    ContDiffOn ℝ ∞ (polarReadout v) (polarReadoutDomain v) := by
  apply ContDiffOn.prodMk
  · exact (angularReadout_contDiffOn v).comp
      (direction_contDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  · exact contDiffOn_const.sub (norm_contDiffOn_compl_zero.mono (fun _ hz => hz.1))

private theorem angularReadout_stereographic (v w : ↥(sphere (0 : X dim) 1)) :
    angularReadout v (w : X dim) = stereographic' (dim - 1) v w := rfl

private theorem direction_polarCollar (v : ↥(sphere (0 : X dim) 1)) (q : AngularCoordinates dim × ℝ)
    (hq : q.2 < 1) :
    direction (polarCollar (angularPoint v) q) = angularPoint v q.1 := by
  have hr : 0 < 1 - q.2 := sub_pos.mpr hq
  rw [direction, polarCollar, norm_smul, Real.norm_of_nonneg hr.le, angularPoint_norm, mul_one,
    smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem polarCollar_mapsTo (v : ↥(sphere (0 : X dim) 1)) :
    MapsTo (polarCollar (angularPoint v)) {q | q.2 < 1} (polarReadoutDomain v) := by
  intro q hq
  have hr : 0 < 1 - q.2 := sub_pos.mpr hq
  have hNorm : ‖polarCollar (angularPoint v) q‖ = 1 - q.2 := by
    rw [polarCollar, norm_smul, Real.norm_of_nonneg hr.le, angularPoint_norm, mul_one]
  refine ⟨norm_ne_zero_iff.mp (hNorm ▸ hr.ne'),?_⟩
  rw [direction_polarCollar v q hq]
  intro h
  let w := (stereographic' (dim - 1) v).symm q.1
  have hWV : w ≠ v := by
    have h := (stereographic' (dim - 1) v).map_target (by simp : q.1 ∈ (stereographic' (dim - 1) v).target)
    simpa [w] using h
  apply hWV
  have hh : ⟪(v : X dim), (w : X dim)⟫_ℝ = 1 := h
  exact (sphere_ext_iff w v).mpr ((real_inner_comm _ _).trans hh)

theorem polarReadout_polarCollar (v : ↥(sphere (0 : X dim) 1)) (q : AngularCoordinates dim × ℝ)
    (hq : q.2 < 1) : polarReadout v (polarCollar (angularPoint v) q) = q := by
  have hr : 0 < 1 - q.2 := sub_pos.mpr hq
  apply Prod.ext
  · change angularReadout v (direction (polarCollar (angularPoint v) q)) = q.1
    rw [direction_polarCollar v q hq]
    exact (stereographic' (dim - 1) v).right_inv (by simp)
  · change 1 - ‖polarCollar (angularPoint v) q‖ = q.2
    rw [polarCollar, norm_smul, Real.norm_of_nonneg hr.le, angularPoint_norm, mul_one]
    ring

theorem polarCollar_polarReadout (v : ↥(sphere (0 : X dim) 1)) {z : X dim} (hz : z ∈ polarReadoutDomain v) :
    polarCollar (angularPoint v) (polarReadout v z) = z := by
  let w : ↥(sphere (0 : X dim) 1) := ⟨direction z, mem_sphere_zero_iff_norm.mpr (direction_norm hz.1)⟩
  have hw : w ∈ (stereographic' (dim - 1) v).source := by
    rw [stereographic'_source]
    intro h
    have h' : w = v := mem_singleton_iff.mp h
    apply hz.2
    change ⟪(v : X dim), (w : X dim)⟫_ℝ = 1
    rw [h', real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v, one_pow]
  have hAngular : angularPoint v (angularReadout v (direction z)) = direction z :=
    congrArg Subtype.val ((stereographic' (dim - 1) v).left_inv hw)
  change (1 - (1 - ‖z‖)) • angularPoint v (angularReadout v (direction z)) = z
  rw [hAngular, show 1 - (1 - ‖z‖) = ‖z‖ by ring, direction, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz.1), one_smul]

/-- Signed spherical boundary coordinates and their exact ambient inverse. -/
def stereographicPolarCollar (v : ↥(sphere (0 : X dim) 1)) :
    OpenPartialHomeomorph (AngularCoordinates dim × ℝ) (X dim) where
  toFun := polarCollar (angularPoint v)
  invFun := polarReadout v
  source := {q | q.2 < 1}
  target := polarReadoutDomain v
  map_source' := polarCollar_mapsTo v
  map_target' {z} hz := by
    change 1 - ‖z‖ < 1
    exact sub_lt_self _ (norm_pos_iff.mpr hz.1)
  left_inv' _ hq := polarReadout_polarCollar v _ hq
  right_inv' _ hz := polarCollar_polarReadout v hz
  open_source := isOpen_lt continuous_snd continuous_const
  open_target := polarReadoutDomain_isOpen v
  continuousOn_toFun := ((contDiff_const.sub contDiff_snd).smul
    ((angularPoint_contDiff v).comp contDiff_fst)).continuous.continuousOn
  continuousOn_invFun := (polarReadout_contDiffOn v).continuousOn

end CalderonPaper
