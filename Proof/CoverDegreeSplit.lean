import DegreeSplitEnvelope
import InterpolateRegular
import RegularFactorEndpoints

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Every degree from zero to D occurs on a spanning factor of this actual
    finite D-regular graph with a perfect matching. -/
theorem all_regular_factors {X : Type*} [Finite X] (H : SimpleGraph X) (D : ℕ)
    (regular : ∀ v, Nat.card (H.neighborSet v)=D) (perfect : ∃ M : H.Subgraph, M.IsPerfectMatching)
    (p : ℕ) (bound : p≤D) : HasFactor H p := by
  obtain ⟨M,hM⟩ := perfect
  obtain ⟨lo,j,k,L,K,eq,jk,hL,hK,degL,degK⟩ := regular_factor_endpoints H D regular M hM p bound
  rw [eq]
  exact factor_interpolation H lo j k jk ⟨L,hL,degL⟩ ⟨K,hK,degK⟩

/-- The bounded-degree split needed by the local potential argument, on
    arbitrary finite hosts with the covering matching explicitly supplied. -/
theorem degree_split_from_cover {X : Type*} [Finite X] (G : SimpleGraph X) (p q : ℕ)
    (bound : ∀ v, Nat.card (G.neighborSet v) ≤ p+q)
    (covered : ∃ M : G.Subgraph, M.IsMatching ∧ ∀ v, Nat.card (G.neighborSet v)=p+q → v∈M.verts) :
    ∃ R : SimpleGraph X, R ≤ G ∧ ∀ v, Nat.card (R.neighborSet v) ≤ p ∧
      Nat.card ((G \ R).neighborSet v) ≤ q := by
  obtain ⟨M,hM,cover⟩ := covered
  let D := p+q
  let H := regularEnvelope G D
  have reg (x) : Nat.card (H.neighborSet x)=D := regularEnvelope_degree G D bound x.1 x.2
  have perf := regularEnvelope_perfectMatching G D M hM bound cover
  obtain ⟨C,sub,deg⟩ := all_regular_factors H D reg perf p (by dsimp [D]; omega)
  exact degreeSplit_of_envelopeFactor G D bound p q rfl C sub deg

#print axioms all_regular_factors
#print axioms degree_split_from_cover
end JSP452Audit.StarHost
