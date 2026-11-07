import SaturationAtTheSameTenDegreeMatchingEndpoint
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem actual_degree_sum_of_palette {X:Type u} [Finite X] (G R:SimpleGraph X) (sub:R≤G) (A:Set X) :
    originalDegreeSum R A+originalDegreeSum (G \ R) A=originalDegreeSum G A := by
  classical
  dsimp only [originalDegreeSum]
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => palette_neighbor_sum G R sub x)

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem target_root_uncovered_count (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) :
    (K.T\M.verts).ncard=K.rootDefect K.T+(K.T∩exposedFull G M 10).ncard := by
  have budget := (K.matching_endpoint_saturation cap M hm attained).2.2.1
  have sum := actual_degree_sum_of_palette G M.spanningCoe M.spanningCoe_le K.T
  rw [matching_degree_sum_eq_covered M hm K.T,budget] at sum
  have union : K.T\M.verts∪(K.T∩M.verts)=K.T := by ext x;by_cases h:x∈M.verts <;> simp [h]
  have dis : Disjoint (K.T\M.verts) (K.T∩M.verts) := Set.disjoint_left.mpr (fun _ a b => a.2 b.2)
  have size := Set.ncard_union_eq dis
  rw [union] at size
  have limit := degree_sum_le_cap G K.T 10 (fun x _ => cap x)
  dsimp only [rootDefect];omega

theorem nonfull_target_root (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) (x:X) (mem:x∈K.T) (nonfull:Nat.card (G.neighborSet x)≠10) :
    Nat.card (G.neighborSet x)=9 ∧ x∉M.verts := by
  classical
  let B := K.T\{x}
  let N := G \ M.spanningCoe
  let W := exposedFull G M 10
  have absent:x∉W := fun hx => nonfull hx.2
  have split : B∪{x}=K.T := by ext y;by_cases eq:y=x <;> simp [B,eq,mem]
  have apart : Disjoint B {x} := Set.disjoint_left.mpr (fun _ a b => a.2 b)
  have size := Set.ncard_union_eq apart
  rw [split,Set.ncard_singleton] at size
  have count : B∩W=K.T∩W := by
    ext y;by_cases eq:y=x
    · subst y;simp [absent]
    · simp [B,eq]
  have total := (K.matching_endpoint_saturation cap M hm attained).2.2.1
  change originalDegreeSum N K.T=9*K.T.ncard+(K.T∩W).ncard at total
  have bound := ten_complement_degree_budget M hm cap B
  change originalDegreeSum N B≤9*B.ncard+(B∩W).ncard at bound
  rw [count] at bound
  have atom := original_degree_sum_of_disjoint_union N B {x} apart
  have sing : originalDegreeSum N {x}=(N.neighborSet x).ncard := by simp [originalDegreeSum]
  rw [split,sing] at atom
  have colors := palette_neighbor_sum G M.spanningCoe M.spanningCoe_le x
  change (M.spanningCoe.neighborSet x).ncard+(N.neighborSet x).ncard=Nat.card (G.neighborSet x) at colors
  have lim := cap x
  refine ⟨by omega,?_⟩
  intro hit
  have yes := matching_neighbor_indicator M hm x
  rw [if_pos hit] at yes
  omega

end TenOuterCut
#print axioms actual_degree_sum_of_palette
#print axioms TenOuterCut.target_root_uncovered_count
#print axioms TenOuterCut.nonfull_target_root
end JSP452Audit.StarHost
