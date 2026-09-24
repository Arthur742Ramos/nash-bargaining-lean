import NashBargaining.Characterization

namespace NashBargaining.Palomar

theorem nashMaximizerExists : ∀ P : Problem, ∃ x, IsNashMaximizer P x :=
  NashBargaining.nashMaximizerExists

theorem nashMaximizerUnique : ∀ P x y, IsNashMaximizer P x → IsNashMaximizer P y → x = y :=
  NashBargaining.nashMaximizerUnique

theorem nashSatisfiesAxioms (F : Problem → ℝ × ℝ) (h : ∀ P, IsNashMaximizer P (F P)) : NashAxioms ⟨F, fun P => (h P).1⟩ :=
  NashBargaining.nashSatisfiesAxioms F h

theorem axiomsCharacterizeNash (F : Solution) (h : NashAxioms F) (P : Problem) (x : ℝ × ℝ) (hx : IsNashMaximizer P x) : F P = x :=
  NashBargaining.axiomsCharacterizeNash F h P x hx

end NashBargaining.Palomar
