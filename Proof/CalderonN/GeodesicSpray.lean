module

public import Proof.CalderonN.Chart

public import Proof.CalderonN.DilationConnection
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace CalderonN

variable {dim : ℕ}

abbrev GeodesicPhase (dim : ℕ) := ℝ × (X dim) × (X dim)

/-- The frozen parameter, position and velocity in the actual chart
geodesic equation. -/
@[expose] def geodesicSpray (γ : ℝ → (MetricField dim)) (q : (GeodesicPhase dim)) : (GeodesicPhase dim) :=
  (0, q.2.2, -connection (γ q.1) q.2.1 q.2.2 q.2.2)

theorem contDiff_geodesicSpray {γ : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hpos : ∀ lam y, (γ lam y).PosDef) :
    ContDiff ℝ ∞ (geodesicSpray γ) := by
  have hΓ (k i j : (I dim)) : ContDiff ℝ ∞
      (fun q : ℝ × (X dim) => christoffel (γ q.1) q.2 k i j) :=
    contDiffOn_univ.mp (contDiffOn_christoffel_slice isOpen_univ
      (fun a b => (hγ a b).contDiffOn) (fun q _ => hpos q.1 q.2) k i j)
  have hp : ContDiff ℝ ∞ (fun q : (GeodesicPhase dim) => (q.1, q.2.1)) :=
    contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)
  have hv : ContDiff ℝ ∞ (fun q : (GeodesicPhase dim) => q.2.2) := contDiff_snd.comp contDiff_snd
  have hconn : ContDiff ℝ ∞
      (fun q : (GeodesicPhase dim) => connection (γ q.1) q.2.1 q.2.2 q.2.2) := by
    rw [← contDiffOn_univ]
    apply (contDiffOn_piLp 2).mpr
    intro k
    change ContDiffOn ℝ ∞ (fun q : (GeodesicPhase dim) =>
      ∑ i, ∑ j, christoffel (γ q.1) q.2.1 k i j * q.2.2 i * q.2.2 j) univ
    exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      ((((hΓ k i j).comp hp).mul ((EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).contDiff.comp hv)).mul
        ((EuclideanSpace.proj j : (X dim) →L[ℝ] ℝ).contDiff.comp hv)).contDiffOn
  exact contDiff_const.prodMk (hv.prodMk hconn.neg)

@[simp] theorem geodesicSpray_rest (γ : ℝ → (MetricField dim)) (lam : ℝ) (y : (X dim)) :
    geodesicSpray γ (lam,y,0) = 0 := by
  simp only [geodesicSpray, connection]
  have he : (WithLp.toLp 2 fun k : (I dim) =>
      ∑ i : (I dim), ∑ j : (I dim), christoffel (γ lam) y k i j * (0 : (X dim)) i * (0 : (X dim)) j) = (0 : (X dim)) := by
    ext k
    simp
  rw [he, neg_zero]
  rfl

/-- The reparametrization of phase space keeps position and multiplies
velocity by the time factor. -/
@[expose] def geodesicPhaseScale (t : ℝ) : (GeodesicPhase dim) →L[ℝ] (GeodesicPhase dim) :=
  (ContinuousLinearMap.fst ℝ ℝ ((X dim) × (X dim))).prod
    ((ContinuousLinearMap.fst ℝ (X dim) (X dim)).prod (t • ContinuousLinearMap.snd ℝ (X dim) (X dim)) |>.comp
      (ContinuousLinearMap.snd ℝ ℝ ((X dim) × (X dim))))

theorem geodesicPhaseScale_apply (t : ℝ) (q : (GeodesicPhase dim)) :
    geodesicPhaseScale t q = (q.1, q.2.1, t • q.2.2) := rfl

theorem geodesicSpray_reparametrize (γ : ℝ → (MetricField dim)) (t : ℝ) (q : (GeodesicPhase dim)) :
    geodesicSpray γ (geodesicPhaseScale t q) = t • geodesicPhaseScale t (geodesicSpray γ q) := by
  rw [geodesicPhaseScale_apply, geodesicPhaseScale_apply]
  refine Prod.ext (by simp [geodesicSpray]) (Prod.ext (by rfl) ?_)
  change -(connection (γ q.1) q.2.1 (t • q.2.2) (t • q.2.2)) =
    t • (t • -connection (γ q.1) q.2.1 q.2.2 q.2.2)
  ext k
  simp only [connection, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, mul_neg, neg_inj,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end CalderonN
