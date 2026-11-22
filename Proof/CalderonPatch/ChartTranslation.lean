module

public import Proof.CalderonN.Chart
import Proof.CalderonN.AffineChart
import Proof.CalderonN.HarmonicL2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

public section

open MeasureTheory Set
open scoped ContDiff

namespace CalderonPatch

open CalderonN

variable {n : ℕ}

theorem smoothMetric_translate {Ω : Set (X n)} {g : MetricField n}
    (hg : CalderonN.SmoothMetric Ω g) (c : X n) :
    CalderonN.SmoothMetric ((c + ·) ⁻¹' Ω) (fun x => g (c + x)) :=
  ⟨fun i j => (hg.1 i j).comp (contDiff_const.add contDiff_id).contDiffOn
    (fun _ hx => hx), fun _ hx => hg.2 _ hx⟩

theorem harmonic_translate {Ω : Set (X n)} {g : MetricField n} {u : X n → ℝ}
    (hu : Harmonic Ω g u) (c : X n) :
    Harmonic ((c + ·) ⁻¹' Ω) (fun x => g (c + x)) (fun x => u (c + x)) :=
  ⟨hu.1.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ hx => hx),
    fun x hx => (laplace_translate g u c x).trans (hu.2 _ hx)⟩

theorem harmonicCoordinates_translate [NeZero n] {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n}
    (hg : HarmonicCoordinates Ω g) (c : X n) :
    HarmonicCoordinates ((c + ·) ⁻¹' Ω) (fun x => g (c + x)) := by
  intro i
  let T := (c + ·) ⁻¹' Ω
  let g' (x : X n) := g (c + x)
  have hT : IsOpen T := hΩ.preimage (continuous_const.add continuous_id)
  have hcoord (j : I n) : coordDeriv j (fun _ : X n => c i) = 0 := by
    funext x
    simp [coordDeriv]
  have hconst : Harmonic T g' (fun _ => c i) :=
    ⟨contDiffOn_const, fun _ _ => by simp [laplace, hcoord, coordDeriv]⟩
  convert (harmonic_translate (hg i) c).sub hT hconst using 1
  ext x
  change x i = c i + x i - c i
  ring

private theorem coordDeriv_translate (c : X n) (u : X n → ℝ) (i : I n) :
    coordDeriv i (fun x => u (c + x)) = fun x => coordDeriv i u (c + x) := by
  funext x
  unfold coordDeriv
  rw [fderiv_comp_add_left]

theorem hessian_translate (c x : X n) (u : X n → ℝ) :
    hessian (fun y => u (c + y)) x = hessian u (c + x) := by
  ext i j
  simp only [hessian, coordDeriv_translate]

private theorem locallyIntegrableOn_translate {Ω : Set (X n)} (hΩ : IsOpen Ω)
    {f : X n → ℝ} (hf : LocallyIntegrableOn f Ω) (c : X n) :
    LocallyIntegrableOn (fun x => f (c + x)) ((c + ·) ⁻¹' Ω) := by
  let A := Homeomorph.addLeft c
  let e := A.toMeasurableEquiv
  have hmap : (volume : Measure (X n)).map e = volume := map_add_left_eq_self volume c
  apply (locallyIntegrableOn_iff (hΩ.preimage A.continuous).isLocallyClosed).mpr
  intro K hKΩ hK
  have hi : IntegrableOn f (e '' K) volume :=
    hf.integrableOn_compact_subset (by rintro _ ⟨x, hx, rfl⟩; exact hKΩ hx)
      (hK.image A.continuous)
  rw [← hmap] at hi
  have hi' := (integrableOn_map_equiv e).mp hi
  rwa [e.injective.preimage_image] at hi'

/-- Recenter the same Green kernel with unit translation Jacobian. -/
theorem greenGerm_translate {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n}
    {G : X n × X n → ℝ} (hG : GreenGerm Ω g G) (c : X n) :
    GreenGerm ((c + ·) ⁻¹' Ω) (fun x => g (c + x))
      (fun p => G (c + p.1, c + p.2)) := by
  let A := Homeomorph.addLeft c
  let e := A.toMeasurableEquiv
  let T : Set (X n) := (c + ·) ⁻¹' Ω
  have hT : IsOpen T := hΩ.preimage A.continuous
  have hmap : (volume : Measure (X n)).map e = volume := map_add_left_eq_self volume c
  have hpair : MapsTo (fun p : X n × X n => (c + p.1, c + p.2))
      (OffDiagonal T) (OffDiagonal Ω) :=
    fun _ hp => ⟨hp.1, hp.2.1, fun h => hp.2.2 (add_left_cancel h)⟩
  have hd : ContDiff ℝ ∞ (fun p : X n × X n => (c + p.1, c + p.2)) :=
    (contDiff_const.add contDiff_fst).prodMk (contDiff_const.add contDiff_snd)
  refine ⟨hG.1.comp hd.contDiffOn hpair, fun _ hp => hG.2.1 _ (hpair hp), ?_⟩
  intro y hy
  refine ⟨locallyIntegrableOn_translate hΩ (hG.2.2 (c + y) hy).1 c, ?_⟩
  intro φ hφ hφc hφT
  let ψ : X n → ℝ := φ ∘ A.symm
  have hψ : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_const.add contDiff_id)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph A.symm
  have hψΩ : tsupport ψ ⊆ Ω := by
    rw [show ψ = φ ∘ A.symm from rfl, tsupport_comp_eq_preimage φ A.symm]
    intro z hz
    have hh : A (A.symm z) ∈ Ω := hφT hz
    rwa [A.apply_symm_apply] at hh
  have hcomp : (fun x => ψ (c + x)) = φ := funext fun x => congrArg φ (A.symm_apply_apply x)
  have hL (x : X n) : laplace (fun z => g (c + z)) φ x = laplace g ψ (c + x) := by
    simpa only [hcomp] using laplace_translate g ψ c x
  let H (x : X n) := G (x, c + y) * (-laplace g ψ x) * Real.sqrt (g x).det
  have hI : (∫ x in T, H (c + x)) = ∫ x in Ω, H x := by
    have he := (setIntegral_map_equiv (μ := (volume : Measure (X n))) e H Ω).symm
    rwa [hmap] at he
  change (∫ x in T, G (c + x, c + y) * (-laplace (fun z => g (c + z)) φ x) *
    Real.sqrt (g (c + x)).det) = φ y
  simp_rw [hL]
  exact hI.trans (((hG.2.2 (c + y) hy).2 ψ hψ hψc hψΩ).trans (congrFun hcomp y))

end CalderonPatch
