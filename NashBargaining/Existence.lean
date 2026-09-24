import NashBargaining.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed

namespace NashBargaining

theorem nashMaximizerExists : ∀ P : Problem, ∃ x, IsNashMaximizer P x := by
  intro P
  rcases P with ⟨⟨S, d⟩, hne, hcomp, hconv, hdS, hstrict⟩
  obtain ⟨x₀, hx₀S, hx₀₁, hx₀₂⟩ := hstrict
  let K : Set (ℝ × ℝ) := S ∩ {x | d.1 ≤ x.1} ∩ {x | d.2 ≤ x.2}
  have hK_nonempty : K.Nonempty := by
    refine ⟨x₀, ?_⟩
    simp only [K, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨⟨hx₀S, le_of_lt hx₀₁⟩, le_of_lt hx₀₂⟩
  have hclosed₁ : IsClosed {x : ℝ × ℝ | d.1 ≤ x.1} :=
    isClosed_le continuous_const continuous_fst
  have hclosed₂ : IsClosed {x : ℝ × ℝ | d.2 ≤ x.2} :=
    isClosed_le continuous_const continuous_snd
  have hK_compact : IsCompact K := by
    dsimp [K]
    exact (hcomp.inter_right hclosed₁).inter_right hclosed₂
  let f : ℝ × ℝ → ℝ := fun x => nashProduct d x
  have hf : ContinuousOn f K := by
    apply Continuous.continuousOn
    dsimp [f, nashProduct]
    exact (continuous_fst.sub continuous_const).mul
      (continuous_snd.sub continuous_const)
  obtain ⟨x, hxK, hmax⟩ := hK_compact.exists_isMaxOn hK_nonempty hf
  refine ⟨x, ?_⟩
  change x ∈ S ∧ d.1 ≤ x.1 ∧ d.2 ≤ x.2 ∧
    ∀ y ∈ S, d.1 ≤ y.1 → d.2 ≤ y.2 → nashProduct d y ≤ nashProduct d x
  rcases hxK with ⟨⟨hxS, hx₁⟩, hx₂⟩
  refine ⟨hxS, hx₁, hx₂, ?_⟩
  intro y hyS hyd₁ hyd₂
  simpa [f] using hmax (by simp [K, hyS, hyd₁, hyd₂])

end NashBargaining
