import NashBargaining.Existence
import NashBargaining.Uniqueness

namespace NashBargaining

theorem nashSatisfiesAxioms (F : Problem → ℝ × ℝ)
    (h : ∀ P, IsNashMaximizer P (F P)) :
    NashAxioms ⟨F, fun P => (h P).1⟩ := sorry

theorem axiomsCharacterizeNash (F : Solution) (h : NashAxioms F)
    (P : Problem) (x : ℝ × ℝ) (hx : IsNashMaximizer P x) : F P = x := sorry

end NashBargaining
