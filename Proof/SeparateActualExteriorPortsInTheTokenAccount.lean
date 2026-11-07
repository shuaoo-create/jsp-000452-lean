import OddUseOfEveryCountedTenDegreePiece
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_complement_degree_budget {X:Type*} [Finite X] {G:SimpleGraph X}
    (M:G.Subgraph) (hm:M.IsMatching) (cap:∀x,Nat.card (G.neighborSet x)≤10) (T:Set X) :
    originalDegreeSum (G \ M.spanningCoe) T≤9*T.ncard+(T∩exposedFull G M 10).ncard := by
  classical
  let R := M.spanningCoe
  let W := exposedFull G M 10
  have point (x:X) : ((G \ R).neighborSet x).ncard≤9+(if x∈W then 1 else 0) := by
    have sum := palette_neighbor_sum G R M.spanningCoe_le x
    have total : (G.neighborSet x).ncard≤10 := cap x
    by_cases missed:x∈W
    · rw [if_pos missed];omega
    · rw [if_neg missed]
      by_cases hit:x∈M.verts
      · have one := matching_neighbor_indicator M hm x
        rw [if_pos hit] at one
        change (R.neighborSet x).ncard=1 at one;omega
      · have low : (G.neighborSet x).ncard≠10 := fun eq => missed ⟨hit,eq⟩
        omega
  have sum := Finset.sum_le_sum (s:=T.toFinite.toFinset) (fun x _ => point x)
  rw [Finset.sum_add_distrib,subset_indicator_sum,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at sum
  have count := (Set.ncard_eq_toFinset_card T T.toFinite).symm
  rw [count,Nat.mul_comm T.ncard 9] at sum
  exact sum


theorem matching_degree_sum_eq_covered {X:Type u} [Finite X] {G:SimpleGraph X} (M:G.Subgraph) (hm:M.IsMatching) (A:Set X) :
    originalDegreeSum M.spanningCoe A=(A∩M.verts).ncard := by
  classical
  change (∑x∈A.toFinite.toFinset,(M.spanningCoe.neighborSet x).ncard)=_
  simp_rw [matching_neighbor_indicator M hm];exact subset_indicator_sum A M.verts

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem split_roots_complement : K.core∪K.supportᶜ=K.rootsᶜ := by
  ext x
  constructor
  · rintro (j|outside);exact K.core_outside j;exact fun a => outside (Or.inl a)
  · intro h;by_cases j:x∈K.core;exact Or.inl j;exact Or.inr (fun ah => ah.elim h j)

theorem root_palette_degrees (H:SimpleGraph X) :
    originalDegreeSum H K.S=2*(H.induce K.S).edgeSet.ncard+crossCount H K.T K.S+
      crossCount H K.core K.S+crossCount H K.S K.supportᶜ ∧
    originalDegreeSum H K.T=2*(H.induce K.T).edgeSet.ncard+crossCount H K.T K.S+
      crossCount H K.core K.T+crossCount H K.T K.supportᶜ := by
  let O := K.rootsᶜ
  have so : Disjoint K.S O := disjoint_compl_right.mono_left Set.subset_union_left
  have to' : Disjoint K.T O := disjoint_compl_right.mono_left Set.subset_union_right
  have all : K.S∪K.T∪O=Set.univ := Set.union_compl_self _
  have ds := partition_handshake H K.S K.T O K.apart so to' all
  have dt := partition_handshake H K.T K.S O K.apart.symm to' so (by rw [Set.union_comm K.T K.S];exact all)
  have dis : Disjoint K.core K.supportᶜ := disjoint_compl_right.mono_left Set.subset_union_right
  have left := cut_cross_union_right H K.S K.core K.supportᶜ dis
  have right := cut_cross_union_right H K.T K.core K.supportᶜ dis
  rw [K.split_roots_complement,crossCount_swap H K.S K.core] at left
  rw [K.split_roots_complement,crossCount_swap H K.T K.core] at right
  rw [crossCount_swap H K.S K.T] at ds
  change crossCount H K.S O=_ at left
  change crossCount H K.T O=_ at right
  omega

theorem matching_token_account (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching) :
    let R := M.spanningCoe
    let N := G \ R
    K.pieces.ncard+crossCount G K.T K.S+2*(R.induce K.S).edgeSet.ncard+2*(N.induce K.T).edgeSet.ncard+
      crossCount R K.S K.supportᶜ+crossCount N K.T K.supportᶜ≤
      (K.S∩M.verts).ncard+originalDegreeSum N K.T+(K.core∩exposedFull G M 10).ncard := by
  intro R N
  have aggregate := K.aggregate_piece_tokens cap M hm
  change K.pieces.ncard≤crossCount R K.core K.S+crossCount N K.core K.T+_ at aggregate
  have red := (K.root_palette_degrees R).1
  have blue := (K.root_palette_degrees N).2
  have split := cross_count_color_partition G R M.spanningCoe_le K.T K.S
  change crossCount G K.T K.S=crossCount R K.T K.S+crossCount N K.T K.S at split
  have eq : originalDegreeSum R K.S=(K.S∩M.verts).ncard := matching_degree_sum_eq_covered M hm K.S
  omega
end TenOuterCut
#print axioms ten_complement_degree_budget
#print axioms matching_degree_sum_eq_covered
#print axioms TenOuterCut.root_palette_degrees
#print axioms TenOuterCut.matching_token_account
end JSP452Audit.StarHost
