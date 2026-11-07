import TwoPhysicalSinglePortNineBlocks
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem matching_neighbor_indicator {X:Type*} [Finite X] {G:SimpleGraph X} (M:G.Subgraph) (hm:M.IsMatching) (x:X) [Decidable (x∈M.verts)] :
    (M.spanningCoe.neighborSet x).ncard=if x∈M.verts then 1 else 0 := by
  classical
  by_cases hit:x∈M.verts
  · obtain ⟨y,e,_⟩ := hm hit
    have pos := (Set.ncard_pos (Set.toFinite _)).mpr (show (M.spanningCoe.neighborSet x).Nonempty from ⟨y,e⟩)
    have one : (M.spanningCoe.neighborSet x).ncard≤1 := spanningMatching_degree_le_one M hm x
    rw [if_pos hit];omega
  · have empty : M.spanningCoe.neighborSet x=∅ := Set.eq_empty_of_forall_notMem (fun _ e => hit (M.edge_vert e))
    rw [if_neg hit,empty,Set.ncard_empty]

theorem subset_indicator_sum {X:Type*} [Finite X] (U W:Set X) [DecidablePred (·∈W)] :
    (∑x∈U.toFinite.toFinset,if x∈W then 1 else 0)=(U∩W).ncard := by
  classical
  have eq : U.toFinite.toFinset.filter (fun x => x∈W)=(U∩W).toFinite.toFinset := by ext x;simp
  rw [←Finset.sum_filter,eq,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one]
  exact (Set.ncard_eq_toFinset_card _ _).symm

theorem matching_degree_sum_and_missed_labels {X:Type*} [Finite X] {G:SimpleGraph X}
    (M:G.Subgraph) (matchM:M.IsMatching) (U:Set X) (D:ℕ)
    (full:∀x∈U,Nat.card (G.neighborSet x)=D) :
    originalDegreeSum M.spanningCoe U+(U∩exposedFull G M D).ncard=U.ncard := by
  classical
  let W := exposedFull G M D
  have point (x) (hx:x∈U) : (M.spanningCoe.neighborSet x).ncard+(if x∈W then 1 else 0)=1 := by
    rw [matching_neighbor_indicator M matchM]
    by_cases hit:x∈M.verts
    · rw [if_pos hit,if_neg (fun mem => (show x∈exposedFull G M D from mem).1 hit)]
    · rw [if_neg hit,if_pos (show x∈W from ⟨hit,full x hx⟩)]
  have sum := Finset.sum_congr (s₁:=U.toFinite.toFinset) rfl (fun x hx => point x (U.toFinite.mem_toFinset.mp hx))
  rw [Finset.sum_add_distrib,subset_indicator_sum U W,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at sum
  have card := (Set.ncard_eq_toFinset_card U U.toFinite).symm
  exact sum.trans card

theorem cross_count_color_partition {X:Type*} [Finite X] (G R:SimpleGraph X) (sub:R≤G) (A B:Set X) :
    crossCount G A B=crossCount R A B+crossCount (G \ R) A B := by
  classical
  let _ := Fintype.ofFinite A
  simp only [crossCount_eq_neighbor_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have dis : Disjoint (R.neighborSet x.val∩B) ((G \ R).neighborSet x.val∩B) := Set.disjoint_left.mpr (fun _ hr hg => hg.1.2 hr.1)
  have eq : (R.neighborSet x.val∩B)∪((G \ R).neighborSet x.val∩B)=G.neighborSet x.val∩B := by
    ext y;constructor
    · rintro (r|b);exact ⟨sub r.1,r.2⟩;exact ⟨b.1.1,b.2⟩
    · intro h;by_cases red:R.Adj x.val y;exact Or.inl ⟨red,h.2⟩;exact Or.inr ⟨⟨h.1,red⟩,h.2⟩
  exact eq ▸ Set.ncard_union_eq dis

theorem palette_boundary_to_actual_roots {X:Type u} [Finite X] (G R:SimpleGraph X) (sub:R≤G) (S T:Set X)
    (dis:Disjoint S T) (C:(G.induce (S∪T)ᶜ).ConnectedComponent) :
    let U := cutPieceSet G (S∪T) C
    crossCount R U Uᶜ=crossCount R U S+crossCount R U T := by
  classical
  intro U
  let A := S∪T
  let _ := Fintype.ofFinite U
  have eq : crossCount R U Uᶜ=crossCount R U A := by
    simp only [crossCount_eq_neighbor_sum]
    apply Finset.sum_congr rfl
    intro x _
    congr 1;ext y
    constructor
    · rintro ⟨adj,out⟩
      refine ⟨adj,?_⟩
      by_contra away;exact out (cut_piece_neighbor G A C x.property (sub adj) away)
    · rintro ⟨adj,inA⟩;exact ⟨adj,fun u => cut_piece_outside G A C u inA⟩
  exact eq.trans (cut_cross_union_right R U S T dis)

#print axioms matching_neighbor_indicator
#print axioms subset_indicator_sum
#print axioms matching_degree_sum_and_missed_labels
#print axioms cross_count_color_partition
#print axioms palette_boundary_to_actual_roots
end JSP452Audit.StarHost
