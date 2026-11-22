module

public import Proof.CalderonN.FiniteRadialModelLinear
public import Proof.CalderonN.FixedBallFluxUnique
public import Proof.CalderonN.SmoothBoundaryLinear

import Mathlib.Tactic

/-! Linearity of the physical normal radial response under any choice
of smooth classical representatives on the common closed unit ball. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem negativeBallDivergence_const_smul_smooth {a : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (b : SmoothData dim) (c : ℝ) (z : X dim) :
    negativeBallDivergence a (c • b.1) z = c*negativeBallDivergence a b.1 z := by
  have hB : fderiv ℝ (c • b.1) = fun x => c • fderiv ℝ b.1 x := by
    funext x
    exact fderiv_const_smul (b.2.differentiable (by simp) x) c
  unfold negativeBallDivergence Elliptic.Lop
  have hFlux (i : Fin dim) :
      (fun x => ∑ j, a x i j * Elliptic.pd j (c • b.1) x) =
        c • (fun x => ∑ j, a x i j * coordDeriv j b.1 x) := by
    funext x
    simp only [Elliptic.pd,coordDeriv,hB,smul_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  simp_rw [hFlux]
  have hDeriv (i : Fin dim) :
      Elliptic.pd i (c • fun x => ∑ j, a x i j * coordDeriv j b.1 x) z =
        c * Elliptic.pd i (fun x => ∑ j, a x i j * coordDeriv j b.1 x) z := by
    have h : ContDiff ℝ ∞ (fun x => ∑ j, a x i j * coordDeriv j b.1 x) :=
      ContDiff.sum fun j _ => (contDiff_pi.mp (contDiff_pi.mp ha i) j).mul (Elliptic.contDiff_pd b.2)
    change fderiv ℝ (c • fun x => ∑ j, a x i j * coordDeriv j b.1 x) z (axis i) = _
    rw [fderiv_const_smul (h.differentiable (by simp) z),smul_apply,smul_eq_mul]
    rfl
  simp_rw [hDeriv,← Finset.mul_sum]
  ring

private def asSmoothBallData (u : SmoothData dim) : smoothBallDataSubmodule dim := ⟨u.1,u.2⟩

private theorem radialResponse_add_eqOn {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hH : ∀ f, EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1))
    (f g : HarmonicFiniteCoefficients dim) :
    EqOn (smoothBallRadialDerivative (b (f+g))).1
      (smoothBallRadialDataL (asSmoothBallData (b f)+asSmoothBallData (b g))).1 (standardSphere dim) := by
  let v := asSmoothBallData (b f)+asSmoothBallData (b g)
  let V : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  have hD : EqOn (negativeBallDivergence a V.1) 0 (ball (0 : X dim) 1) := by
    intro x hx
    change negativeBallDivergence a ((b f).1+(b g).1) x = 0
    rw [negativeBallDivergence_add ha (b f).2 (b g).2,
      show negativeBallDivergence a (b f).1 x = 0 from hH f hx,
      show negativeBallDivergence a (b g).1 x = 0 from hH g hx,add_zero]
  have hBV : EqOn (b (f+g)).1 V.1 (standardSphere dim) := by
    intro z hz
    change (b (f+g)).1 z = (b f).1 z+(b g).1 z
    rw [hT (f+g) hz,hT f hz,hT g hz,← harmonicFiniteSmoothL_val,← harmonicFiniteSmoothL_val,
      ← harmonicFiniteSmoothL_val,map_add]
    rfl
  rw [smoothBallRadialDataL_val]
  exact eqOn_radialDerivative_of_classicalNormalResponses ha hEll (fun _ _ => rfl)
    (b (f+g)) V (hH _) hD hBV

private theorem radialResponse_smul_eqOn {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hH : ∀ f, EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1))
    (c : ℝ) (f : HarmonicFiniteCoefficients dim) :
    EqOn (smoothBallRadialDerivative (b (c • f))).1
      (smoothBallRadialDataL (c • asSmoothBallData (b f))).1 (standardSphere dim) := by
  let v := c • asSmoothBallData (b f)
  let V : SmoothData dim := ⟨v.1,smoothBallData_contDiff v⟩
  have hD : EqOn (negativeBallDivergence a V.1) 0 (ball (0 : X dim) 1) := by
    intro x hx
    change negativeBallDivergence a (c • (b f).1) x = 0
    rw [negativeBallDivergence_const_smul_smooth ha (b f) c,
      show negativeBallDivergence a (b f).1 x = 0 from hH f hx,mul_zero]
  have hBV : EqOn (b (c • f)).1 V.1 (standardSphere dim) := by
    intro z hz
    change (b (c • f)).1 z = c*(b f).1 z
    rw [hT (c • f) hz,hT f hz,← harmonicFiniteSmoothL_val,← harmonicFiniteSmoothL_val,map_smul]
    rfl
  rw [smoothBallRadialDataL_val]
  exact eqOn_radialDerivative_of_classicalNormalResponses ha hEll (fun _ _ => rfl)
    (b (c • f)) V (hH _) hD hBV

/-- A linear operator on the radial trace gives a finite boundary map
whenever it respects equality on the sphere. -/
def finiteMappedRadialResponseL (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (B : smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim)
    (hB : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → EqOn (B u).1 (B v).1 (standardSphere dim))
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hH : ∀ f, EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1)) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim s where
  toFun f := smoothBoundarySobolevLinear hn s hs (B (smoothBallRadialDataL (asSmoothBallData (b f))))
  map_add' f g := by
    let L := smoothBoundarySobolevLinear hn s hs
    let v := smoothBallRadialDataL (asSmoothBallData (b f)+asSmoothBallData (b g))
    let w := smoothBallRadialDataL (asSmoothBallData (b (f+g)))
    have he : EqOn w.1 v.1 (standardSphere dim) := radialResponse_add_eqOn ha hEll b hT hH f g
    have h := smoothBoundarySobolev_eq_of_eqOn hn s hs
      ⟨(B w).1,smoothBallData_contDiff (B w)⟩ ⟨(B v).1,smoothBallData_contDiff (B v)⟩ (hB w v he)
    change L (B w) = L (B (smoothBallRadialDataL (asSmoothBallData (b f))))+
      L (B (smoothBallRadialDataL (asSmoothBallData (b g))))
    rw [show L (B w) = L (B v) from h]
    simp only [v,map_add]
  map_smul' c f := by
    let L := smoothBoundarySobolevLinear hn s hs
    let v := smoothBallRadialDataL (c • asSmoothBallData (b f))
    let w := smoothBallRadialDataL (asSmoothBallData (b (c • f)))
    have he : EqOn w.1 v.1 (standardSphere dim) := radialResponse_smul_eqOn ha hEll b hT hH c f
    have h := smoothBoundarySobolev_eq_of_eqOn hn s hs
      ⟨(B w).1,smoothBallData_contDiff (B w)⟩ ⟨(B v).1,smoothBallData_contDiff (B v)⟩ (hB w v he)
    change L (B w) = c • L (B (smoothBallRadialDataL (asSmoothBallData (b f))))
    rw [show L (B w) = L (B v) from h]
    simp only [v,map_smul]

theorem finiteMappedRadialResponseL_apply (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (B : smoothBallDataSubmodule dim →ₗ[ℝ] smoothBallDataSubmodule dim)
    (hB : ∀ u v, EqOn u.1 v.1 (standardSphere dim) → EqOn (B u).1 (B v).1 (standardSphere dim))
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hH : ∀ f, EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1))
    (f : HarmonicFiniteCoefficients dim) :
    finiteMappedRadialResponseL hn s hs B hB ha hEll b hT hH f =
      smoothBoundarySobolevLinear hn s hs
        (B (smoothBallRadialDataL (⟨(b f).1,(b f).2⟩ : smoothBallDataSubmodule dim))) := by
  unfold finiteMappedRadialResponseL asSmoothBallData
  rfl

/-- The actual classical radial trace on finite harmonic inputs. -/
def finiteRadialResponseL (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hH : ∀ f, EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1)) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim s :=
  finiteMappedRadialResponseL hn s hs LinearMap.id (fun _ _ h => h) ha hEll b hT hH

theorem finiteRadialResponseL_apply (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) a lo hi)
    (b : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hH : ∀ f, EqOn (negativeBallDivergence a (b f).1) 0 (ball (0 : X dim) 1))
    (f : HarmonicFiniteCoefficients dim) :
    finiteRadialResponseL hn s hs ha hEll b hT hH f =
      smoothBoundarySobolev hn s hs (smoothBallRadialDerivative (b f)) := by
  rw [finiteRadialResponseL,finiteMappedRadialResponseL_apply,LinearMap.id_apply,
    smoothBoundarySobolevLinear_apply]
  rfl

end CalderonN
