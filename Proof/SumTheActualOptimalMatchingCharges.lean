import ActualMatchingChargesInNineCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem cross_le_original_degree_sum {X:Type*} [Finite X] (G:SimpleGraph X) (S V:Set X) :
    crossCount G S V≤originalDegreeSum G S := by
  classical
  let _ := Fintype.ofFinite S
  rw [crossCount_eq_neighbor_sum]
  have bound := Finset.sum_le_sum (s:=(Finset.univ:Finset S))
    (fun x _ => Set.ncard_le_ncard (Set.inter_subset_left (s:=G.neighborSet x.val) (t:=V)))
  have eq : originalDegreeSum G S=∑x:↥S,(G.neighborSet x.val).ncard :=
    Finset.sum_subtype S.toFinite.toFinset (fun _ => S.toFinite.mem_toFinset) (fun x => (G.neighborSet x).ncard)
  rw [eq];exact bound

theorem complement_of_matching_degree_budget {X:Type*} [Finite X] {G:SimpleGraph X}
    (M:G.Subgraph) (hm:M.IsMatching) (cap:∀x,Nat.card (G.neighborSet x)≤9) (T:Set X) :
    originalDegreeSum (G \ M.spanningCoe) T≤8*T.ncard+(T∩exposedFull G M 9).ncard := by
  classical
  let R := M.spanningCoe
  let W := exposedFull G M 9
  have point (x:X) : ((G \ R).neighborSet x).ncard≤8+(if x∈W then 1 else 0) := by
    have sum := palette_neighbor_sum G R M.spanningCoe_le x
    have total : (G.neighborSet x).ncard≤9 := cap x
    by_cases missed:x∈W
    · rw [if_pos missed];omega
    · rw [if_neg missed]
      by_cases hit:x∈M.verts
      · have one := matching_neighbor_indicator M hm x
        rw [if_pos hit] at one
        change (R.neighborSet x).ncard=1 at one;omega
      · have low : (G.neighborSet x).ncard≠9 := fun eq => missed ⟨hit,eq⟩
        omega
  have sum := Finset.sum_le_sum (s:=T.toFinite.toFinset) (fun x _ => point x)
  rw [Finset.sum_add_distrib,subset_indicator_sum,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at sum
  have count := (Set.ncard_eq_toFinset_card T T.toFinite).symm
  rw [count,Nat.mul_comm T.ncard 8] at sum
  exact sum

namespace NineOriginalCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:NineOriginalCut G)

theorem matching_use_global (cap:∀x,Nat.card (G.neighborSet x)≤9) (M:G.Subgraph) (hm:M.IsMatching)
    (optimal:(exposedFull G M 9).ncard=minimumExposure G 9) [Fintype ↥K.blocks] :
    (∑c:↥K.blocks,K.matchingUse M c)+crossCount G K.T K.S≤K.S.ncard+8*K.T.ncard+minimumExposure G 9 := by
  classical
  let R := M.spanningCoe
  let N := G \ R
  let W := exposedFull G M 9
  let J := K.region
  have out : J⊆K.barrierᶜ := by rintro _ ⟨v,rfl,_⟩;exact v.property
  have jS : Disjoint K.S J := disjoint_compl_right.mono Set.subset_union_left out
  have jT : Disjoint K.T J := disjoint_compl_right.mono Set.subset_union_right out
  have red := cross_from_root_bound R 1 (spanningMatching_degree_le_one M hm) K.S (K.T∪J)
    (Set.disjoint_union_right.mpr ⟨K.apart,jS⟩)
  rw [cut_cross_union_right R K.S K.T J jT,crossCount_swap R K.S K.T,crossCount_swap R K.S J,Nat.one_mul] at red
  have blue := (cross_le_original_degree_sum N K.T (K.S∪J)).trans (complement_of_matching_degree_budget M hm cap K.T)
  rw [cut_cross_union_right N K.T K.S J jS,crossCount_swap N K.T J] at blue
  have split := cross_count_color_partition G R M.spanningCoe_le K.T K.S
  change crossCount G K.T K.S=crossCount R K.T K.S+crossCount N K.T K.S at split
  have disjointW : Disjoint (K.T∩W) (J∩W) := jT.mono Set.inter_subset_left Set.inter_subset_left
  have unpaid := Set.ncard_le_ncard (show (K.T∩W)∪(J∩W)⊆W from Set.union_subset Set.inter_subset_right Set.inter_subset_right)
  rw [Set.ncard_union_eq disjointW,optimal] at unpaid
  have s := selected_color_cross_sum G R K.barrier K.blocks K.S
  have t := selected_color_cross_sum G N K.barrier K.blocks K.T
  have misses := selected_piece_intersections G K.barrier K.blocks W
  change crossCount R J K.S=∑c:↥K.blocks,crossCount R (K.labels c) K.S at s
  change crossCount N J K.T=∑c:↥K.blocks,crossCount N (K.labels c) K.T at t
  change (J∩W).ncard=∑c:↥K.blocks,(K.labels c∩W).ncard at misses
  change (∑c:↥K.blocks,(crossCount R (K.labels c) K.S+crossCount N (K.labels c) K.T+(K.labels c∩W).ncard))+_≤_
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←s,←t,←misses]
  change crossCount N K.T K.S+crossCount N J K.T≤8*K.T.ncard+(K.T∩W).ncard at blue
  omega

#print axioms matching_use_global
end NineOriginalCut
#print axioms cross_le_original_degree_sum
#print axioms complement_of_matching_degree_budget
end JSP452Audit.StarHost
