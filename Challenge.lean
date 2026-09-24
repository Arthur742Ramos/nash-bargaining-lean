import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace NashBargaining

def Problem : Type :=
  { p : Set (ℝ × ℝ) × (ℝ × ℝ) //
    p.1.Nonempty ∧ IsCompact p.1 ∧ Convex ℝ p.1 ∧ p.2 ∈ p.1 ∧
      ∃ x ∈ p.1, p.2.1 < x.1 ∧ p.2.2 < x.2 }

def nashProduct (d x : ℝ × ℝ) : ℝ := (x.1 - d.1) * (x.2 - d.2)

def IsNashMaximizer (P : Problem) (x : ℝ × ℝ) : Prop :=
  x ∈ P.val.1 ∧ P.val.2.1 ≤ x.1 ∧ P.val.2.2 ≤ x.2 ∧
    ∀ y ∈ P.val.1, P.val.2.1 ≤ y.1 → P.val.2.2 ≤ y.2 →
      nashProduct P.val.2 y ≤ nashProduct P.val.2 x

def Solution : Type := { F : Problem → ℝ × ℝ // ∀ P, F P ∈ P.val.1 }

instance : CoeFun Solution fun _ => Problem → ℝ × ℝ where
  coe F := F.val

def Pareto (F : Solution) : Prop :=
  ∀ P : Problem, ∀ y ∈ P.val.1, (F P).1 ≤ y.1 ∧ (F P).2 ≤ y.2 → y = F P

def Symmetric (F : Solution) : Prop :=
  ∀ P : Problem, Prod.swap '' P.val.1 = P.val.1 → P.val.2.1 = P.val.2.2 →
    (F P).1 = (F P).2

def Invariance (F : Solution) : Prop :=
  ∀ P Q : Problem, ∀ a1 a2 b1 b2 : ℝ, 0 < a1 → 0 < a2 →
    Q.val.1 = (fun x : ℝ × ℝ => (a1 * x.1 + b1, a2 * x.2 + b2)) '' P.val.1 →
    Q.val.2 = (a1 * P.val.2.1 + b1, a2 * P.val.2.2 + b2) →
    F Q = (a1 * (F P).1 + b1, a2 * (F P).2 + b2)

def IIA (F : Solution) : Prop :=
  ∀ P Q : Problem, P.val.2 = Q.val.2 → P.val.1 ⊆ Q.val.1 → F Q ∈ P.val.1 →
    F P = F Q

def NashAxioms (F : Solution) : Prop :=
  Pareto F ∧ Symmetric F ∧ Invariance F ∧ IIA F

end NashBargaining

namespace NashBargaining.Palomar

theorem nashMaximizerExists : ∀ P : Problem, ∃ x, IsNashMaximizer P x := sorry

theorem nashMaximizerUnique : ∀ P x y, IsNashMaximizer P x → IsNashMaximizer P y → x = y := sorry

theorem nashSatisfiesAxioms (F : Problem → ℝ × ℝ) (h : ∀ P, IsNashMaximizer P (F P)) : NashAxioms ⟨F, fun P => (h P).1⟩ := sorry

theorem axiomsCharacterizeNash (F : Solution) (h : NashAxioms F) (P : Problem) (x : ℝ × ℝ) (hx : IsNashMaximizer P x) : F P = x := sorry

end NashBargaining.Palomar
