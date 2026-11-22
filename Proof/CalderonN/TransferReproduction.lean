module

public import Proof.CalderonN.Chart
public import Proof.CalderonN.Moments
public import Proof.CalderonN.SphereFrame

import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The same real transfer functional tested against a fixed harmonic
function; the sphere argument uses the protected exponential map and radius. -/
@[expose] def transferValue (d : (Data dim)) (ψ : (Field dim)) (u : (X dim) → ℝ) (y : (X dim)) : ℝ :=
  ∫ w : ↥(standardSphere dim), (ψ (y,frameVector d.frame y w)).re *
    u (endpoint d.expMap d.radius (y,frameVector d.frame y w)) ∂(sphereProbability dim)

/-- Green's identity on the known side and local harmonicity of the same
transfer functional propagate reproduction to every center. -/
theorem transferValue_eq_of_known_open
    {Y V : Set (X dim)} (hY : IsOpen Y) (hconn : IsConnected Y)
    (hV : IsOpen V) (hne : V.Nonempty) (hVY : V ⊆ Y)
    {d : (Data dim)} (hg : SmoothMetric Y d.g₂)
    {ψ : (Field dim)} {u v : (X dim) → ℝ} (htransfer : Harmonic Y d.g₂ (transferValue d ψ u))
    (hv : Harmonic Y d.g₂ v) (hseed : EqOn (transferValue d ψ u) u V) (hmatch : EqOn u v V) :
    EqOn (transferValue d ψ u) v Y :=
  harmonic_eqOn_of_eqOn_open hY hconn hV hne hVY hg htransfer hv (hseed.trans hmatch)

theorem harmonic_one (Y : Set (X dim)) (g : (MetricField dim)) :
    Harmonic Y g (fun _ => (1 : ℝ)) := by
  refine ⟨contDiffOn_const, fun x _ => ?_⟩
  have hz (i : (I dim)) : coordDeriv i (fun _ : (X dim) => (1 : ℝ)) = 0 := by
    funext y
    simp [coordDeriv]
  simp [laplace, hz, coordDeriv]

/-- Simultaneous constant, coordinate and paired reproduction from the
same locally harmonic transfer on a connected center patch. -/
theorem transfer_reproduces_harmonic_family
    {Y V : Set (X dim)} (hY : IsOpen Y) (hconn : IsConnected Y)
    (hV : IsOpen V) (hne : V.Nonempty) (hVY : V ⊆ Y)
    {d : (Data dim)} (hg : SmoothMetric Y d.g₂)
    (hcoord : HarmonicCoordinates Y d.g₂) {ψ : (Field dim)} {n : ℕ}
    {u v : Fin n → (X dim) → ℝ} (hv : ∀ a, Harmonic Y d.g₂ (v a)) (hmatch : ∀ a, EqOn (u a) (v a) V)
    (hlocal : ∀ f ∈ ({fun _ : (X dim) => (1 : ℝ)} ∪ range (fun i : (I dim) => fun x : (X dim) => x i) ∪ range u),
      Harmonic Y d.g₂ (transferValue d ψ f))
    (hlower : ∀ f ∈ ({fun _ : (X dim) => (1 : ℝ)} ∪ range (fun i : (I dim) => fun x : (X dim) => x i) ∪ range u),
      EqOn (transferValue d ψ f) f V) :
    EqOn (transferValue d ψ (fun _ => 1)) 1 Y ∧
      (∀ i : (I dim), EqOn (transferValue d ψ (fun x => x i)) (fun x => x i) Y) ∧
      ∀ a, EqOn (transferValue d ψ (u a)) (v a) Y := by
  have hone : (fun _ : (X dim) => (1 : ℝ)) ∈
      ({fun _ : (X dim) => (1 : ℝ)} ∪ range (fun i : (I dim) => fun x : (X dim) => x i) ∪ range u) :=
    Or.inl (Or.inl (mem_singleton _))
  have hcoords (i : (I dim)) : (fun x : (X dim) => x i) ∈
      ({fun _ : (X dim) => (1 : ℝ)} ∪ range (fun i : (I dim) => fun x : (X dim) => x i) ∪ range u) :=
    Or.inl (Or.inr (mem_range_self i))
  exact ⟨transferValue_eq_of_known_open hY hconn hV hne hVY hg
      (hlocal _ hone) (harmonic_one Y _) (hlower _ hone) (fun _ _ => rfl),
    fun i => transferValue_eq_of_known_open hY hconn hV hne hVY hg
      (hlocal _ (hcoords i)) (hcoord i) (hlower _ (hcoords i)) (fun _ _ => rfl),
    fun a => transferValue_eq_of_known_open hY hconn hV hne hVY hg
      (hlocal _ (Or.inr (mem_range_self a))) (hv a) (hlower _ (Or.inr (mem_range_self a))) (hmatch a)⟩

end CalderonN
