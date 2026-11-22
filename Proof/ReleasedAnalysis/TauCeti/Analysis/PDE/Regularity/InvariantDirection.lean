/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Regularity.Basic
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Ellipticity.LipschitzReading
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyForm.InvariantDifferenceQuotient
import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.DifferenceQuotient

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Gradient NNReal
namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {A : Matrix ι ι ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {lam Lam : ℝ} {K : ℝ≥0}

/-- **Discrete integration by parts for a Lipschitz coefficient field.** Testing the difference
quotient of `u` against `v` is the same, up to sign, as testing `u` against the difference
quotient of `v` with the opposite step, with an error controlled by the Lipschitz constant `K` of
`x ↦ a(x)`:

`|a(Dᵗ u, v) + a(u, D⁻ᵗ v)| ≤ K ‖w‖ ‖∇u‖_{L²} ‖∇v‖_{L²}`.

The error is the energy form of the difference quotient of the coefficient field, which is
bounded by `K ‖w‖` uniformly in the step `t`. For a constant coefficient it vanishes
(`TauCeti.PDE.energyFormH1_differenceQuotient_eq_neg`). The coefficient field needs essentially
bounded energy densities on the invariant domain and
Lipschitz bilinear forms there; its values outside the domain are unrestricted. -/
theorem abs_energyFormH1_differenceQuotient_add_le
    {Omega : Opens (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι}
    (hw : ∀ t : ℝ, MapsTo (· + t • w) Omega Omega)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega) (t : ℝ)
    (u v : W1p mu Omega 2) :
    |energyFormH1 a 0 0 (W1p.differenceQuotient le_rfl w t (hw t) u) v
        + energyFormH1 a 0 0 u
          (W1p.differenceQuotient le_rfl w (-t) (hw (-t)) v)|
      ≤ K * ‖w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient v‖ := by
  have hOmega : ∀ s : ℝ, (Omega : Set (EuclideanSpace ℝ ι)) =
      (· + s • w) ⁻¹' Omega := fun s => Set.ext fun x =>
    ⟨fun hx => hw s hx, fun hx => by
      simpa [neg_smul, add_assoc] using hw (-s) hx⟩
  have hk : t • w + (-t) • w = 0 := by rw [← add_smul]; simp
  -- What survives is the change of the energy form under translating the coefficient field,
  -- tested against `u` and the translate `τ` of `v`.
  rw [energyFormH1_differenceQuotient_left (b := 0) (c := 0) hcoeff,
    energyFormH1_differenceQuotient_right (b := 0) (c := 0) hcoeff,
    energyFormH1_translate_invariant a hk (hOmega t) (hh := hw t) (hkOmega := hw (-t))]
  set τ := W1p.translate (hw (-t)) v
  rw [show ∀ X Y Z : ℝ, t⁻¹ * (X - Y) + (-t)⁻¹ * (Z - Y) = t⁻¹ * (X - Z) by
    intro X Y Z; rw [inv_neg]; ring]
  -- Translation preserves the `L²` norm of the gradient.
  have hτ : ‖W1p.gradient τ‖ = ‖W1p.gradient v‖ := by
    have hres : MeasurePreserving (· + (-t) • w)
        (mu.restrict Omega) (mu.restrict Omega) :=
      by simpa only [← hOmega (-t)] using
        (measurePreserving_add_right mu ((-t) • w)).restrict_preimage Omega.isOpen.measurableSet
    have heq : W1p.gradient τ =
        Lp.compMeasurePreserving (· + (-t) • w) hres (W1p.gradient v) :=
      Lp.ext ((W1p.gradient_translate_ae _ v).trans
        (Lp.coeFn_compMeasurePreserving _ _).symm)
    rw [heq, Lp.norm_compMeasurePreserving]
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [inv_zero, zero_mul, abs_zero]
    positivity
  rw [abs_mul, abs_inv]
  calc _ ≤ |t|⁻¹ * (K * ‖(-t) • w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient τ‖) := by
        gcongr
        simpa only [Real.norm_eq_abs] using
          norm_energyFormH1_comp_add_sub_le_invariant hcoeff hK _ (hOmega (-t)) u τ
    _ = K * ‖w‖ * ‖W1p.gradient u‖ * ‖W1p.gradient v‖ := by
        rw [hτ, norm_smul, norm_neg, Real.norm_eq_abs]
        field_simp
theorem UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzOnWith_of_mapsTo
    [DecidableEq ι] {Omega : Opens (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι}
    (hw : ∀ t : ℝ, MapsTo (· + t • w) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (t : ℝ) :
    ‖W1p.gradient (W1p.differenceQuotient le_rfl w t (hw t) (u : W1p mu Omega 2))‖ ≤
      ‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam := by
  have hlam := ha.pos
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix ι ι ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → ι → ℝ))
  have hmeas : AEStronglyMeasurable a (mu.restrict Omega) :=
    (continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
      Omega.isOpen.measurableSet
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega) :=
    memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0) ha.upper_nonneg hmeas
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x hx => ha.upper_bound hx) (fun _ _ => by simp) (fun _ _ => by simp)
  have hrev : ∀ s : ℝ, ∀ x, x + s • w ∈ Omega → x ∈ Omega := fun s x hx => by
    simpa [neg_smul, add_assoc] using hw (-s) hx
  -- The difference quotient `g = Dᵗ u` and the test function `v = D⁻ᵗ g`, both in `H¹₀(Ω)`.
  obtain ⟨g, hg0⟩ : ∃ g : W1p0 mu Omega 2,
      (g : W1p mu Omega 2) = W1p.differenceQuotient le_rfl w t (hw t) (u : W1p mu Omega 2) :=
    ⟨⟨_, W1p.differenceQuotient_mem_w1p0Submodule (hw t) (hrev t) u.2⟩, rfl⟩
  obtain ⟨v, hv0⟩ : ∃ v : W1p0 mu Omega 2,
      (v : W1p mu Omega 2) = W1p.differenceQuotient le_rfl w (-t) (hw (-t)) (g : W1p mu Omega 2) :=
    ⟨⟨_, W1p.differenceQuotient_mem_w1p0Submodule (hw (-t)) (hrev (-t)) g.2⟩, rfl⟩
  -- Discrete integration by parts is performed on the invariant domain itself.
  have hDQ := abs_energyFormH1_differenceQuotient_add_le hw hcoeff hK t
    (u : W1p mu Omega 2) (g : W1p mu Omega 2)
  rw [← hg0, ← hv0] at hDQ
  -- Ellipticity on `Ω` bounds the Dirichlet energy of the difference quotient from below.
  have hlow : lam * ‖W1p.gradient (g : W1p mu Omega 2)‖ ^ 2 ≤
      energyFormH1 a 0 0 (g : W1p mu Omega 2) (g : W1p mu Omega 2) :=
    mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (gamma := 0) ha
      hmeas
      aestronglyMeasurable_const (fun _ _ => rfl) (fun _ _ => by simp) (fun _ _ => le_rfl) _
  -- The weak equation, tested against `v`.
  have hsol : energyFormH1 a 0 0 (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
      ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
    have h1 := (isWeakSolutionDirichlet_iff f u).mp hu v
    rwa [← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply] at h1
  -- Cauchy--Schwarz and the difference-quotient bound on the value.
  have hdq : ‖W1p.value (v : W1p mu Omega 2)‖ ≤ ‖w‖ * ‖W1p.gradient (g : W1p mu Omega 2)‖ :=
    hv0 ▸ W1p0.norm_value_differenceQuotient_le (by norm_num) (hw (-t)) (hrev (-t)) g
  have hf : |⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ| ≤
      ‖f‖ * (‖w‖ * ‖W1p.gradient (g : W1p mu Omega 2)‖) :=
    (abs_real_inner_le_norm f _).trans (by gcongr)
  have hkey : lam * ‖W1p.gradient (g : W1p mu Omega 2)‖ ^ 2 ≤
      ‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) *
        ‖W1p.gradient (g : W1p mu Omega 2)‖ := by
    have h1 := (abs_le.1 hDQ).2
    have h2 := (abs_le.1 hf).1
    rw [hsol] at h1
    linarith
  rw [← hg0]
  rcases eq_or_lt_of_le (norm_nonneg (W1p.gradient (g : W1p mu Omega 2))) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (by positivity) hlam.le
  · rw [le_div_iff₀ hlam]
    exact le_of_mul_le_mul_right (by linarith) hpos

/-- **The difference quotients of the gradient of a weak solution are uniformly bounded.** Let
`a` be uniformly elliptic on the whole space with lower constant `λ`, and let `x ↦ a(x)` be
`K`-Lipschitz in the operator norm of its bilinear forms. For a weak solution `u ∈ H¹(ℝⁿ)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f`,

`‖∇Dᵗ u‖_{L²} ≤ ‖w‖ (‖f‖_{L²} + K ‖∇u‖_{L²}) / λ`

for every direction `w` and every step `t`, the bound being independent of `t`. Since
`∇Dᵗ u = Dᵗ ∇u`, this is the uniform difference-quotient bound on the gradient that the
difference-quotient criterion turns into a second weak derivative.

On the whole space `H¹₀(ℝⁿ) = H¹(ℝⁿ)`, so the hypothesis imposes no boundary condition; it is
exactly the weak equation tested against every `H¹(ℝⁿ)` function. This is the case `Ω = ℝⁿ` of
`TauCeti.PDE.UniformlyEllipticOn.norm_gradient_differenceQuotient_le_of_lipschitzOnWith_of_mapsTo`.
-/
theorem UniformlyEllipticOn.exists_norm_le_hasWeakLineDerivOn_gradient_of_lipschitzOnWith_of_mapsTo
    [DecidableEq ι] {Omega : Opens (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι}
    (hw : ∀ t : ℝ, MapsTo (· + t • w) Omega Omega)
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a 0 0 f u) (y : EuclideanSpace ℝ ι) :
    ∃ G : Lp ℝ 2 (mu.restrict Omega),
      ‖G‖ ≤ ‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam) ∧
        HasWeakLineDerivOn mu Omega
          (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ) G w := by
  have hlam := ha.pos
  have hloc : LocallyIntegrableOn (fun x => ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ)
      (Omega : Set (EuclideanSpace ℝ ι)) mu := by
    simpa using
      ((W1p.hasWeakFDerivOn (u : W1p mu Omega 2)).hasWeakLineDerivOn y).locallyIntegrableOn_deriv
  -- The uniform bound on the difference quotients of `∂_y u`, on all of `Ω`.
  have hglobal : ∀ t : ℝ, eLpNorm
      (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu Omega 2) (x + t • w), y⟫_ℝ
        - ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ)) 2 (mu.restrict Omega)
      ≤ ENNReal.ofReal
        (‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam)) := by
    intro t
    set g := W1p.differenceQuotient le_rfl w t (hw t) (u : W1p mu Omega 2)
    have hae : (fun x => t⁻¹ * (⟪W1p.gradient (u : W1p mu Omega 2) (x + t • w), y⟫_ℝ
          - ⟪W1p.gradient (u : W1p mu Omega 2) x, y⟫_ℝ))
        =ᵐ[mu.restrict Omega] fun x => ⟪W1p.gradient g x, y⟫_ℝ := by
      filter_upwards [W1p.gradient_differenceQuotient_ae le_rfl w t (hw t)
        (u : W1p mu Omega 2)] with x hx
      rw [hx, inner_smul_left, inner_sub_left]
      simp [mul_sub]
    rw [eLpNorm_congr_ae hae]
    calc eLpNorm (fun x => ⟪W1p.gradient g x, y⟫_ℝ) 2 (mu.restrict Omega)
        ≤ eLpNorm (‖y‖ • (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)) 2
            (mu.restrict Omega) :=
          have hmeas : AEStronglyMeasurable (fun x => ⟪W1p.gradient g x, y⟫_ℝ)
              (mu.restrict Omega) :=
            (Lp.aestronglyMeasurable (W1p.gradient g)).inner_const
          eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall fun x => by
            rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm, mul_comm]
            exact abs_real_inner_le_norm _ y)
      _ = ‖y‖ₑ * eLpNorm (W1p.gradient g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
            (mu.restrict Omega) := by
          rw [eLpNorm_const_smul, enorm_norm]
      _ = ‖y‖ₑ * ENNReal.ofReal ‖W1p.gradient g‖ := by
          rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      _ ≤ ‖y‖ₑ * ENNReal.ofReal
            (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam) := by
          gcongr
          exact ha.norm_gradient_differenceQuotient_le_of_lipschitzOnWith_of_mapsTo hw hK hu t
      _ = ENNReal.ofReal
            (‖y‖ * (‖w‖ * (‖f‖ + K * ‖W1p.gradient (u : W1p mu Omega 2)‖) / lam)) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg y)]
  refine exists_norm_le_hasWeakLineDerivOn_of_frequently_eLpNorm_inv_mul_sub_le hloc w
    (by positivity) fun S hS _ => Filter.Eventually.frequently ?_
  filter_upwards with t
  exact le_trans (eLpNorm_mono_measure _ (Measure.restrict_mono hS le_rfl)) (hglobal t)

end PDE
end TauCeti
