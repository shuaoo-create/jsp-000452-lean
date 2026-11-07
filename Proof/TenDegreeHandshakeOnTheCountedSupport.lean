import TheActualTenDegreeOuterCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem cut_partition :
    crossCount G K.rootsᶜ K.roots=crossCount G K.core K.roots+crossCount G K.supportᶜ K.roots := by
  have eq : K.core∪K.supportᶜ=K.rootsᶜ := by
    ext x
    constructor
    · rintro (j|outside);exact K.core_outside j;exact fun a => outside (Or.inl a)
    · intro h;by_cases j:x∈K.core;exact Or.inl j;exact Or.inr (fun ah => ah.elim h j)
  have dis : Disjoint K.core K.supportᶜ := disjoint_compl_right.mono_left Set.subset_union_right
  have split := cut_cross_union_right G K.roots K.core K.supportᶜ dis
  rw [eq,crossCount_swap G K.roots K.rootsᶜ,crossCount_swap G K.roots K.core,crossCount_swap G K.roots K.supportᶜ] at split
  exact split

theorem root_degree_account :
    originalDegreeSum G K.S+originalDegreeSum G K.T=
    2*(G.induce K.S).edgeSet.ncard+2*(G.induce K.T).edgeSet.ncard+
      2*crossCount G K.T K.S+crossCount G K.rootsᶜ K.roots := by
  let O := K.rootsᶜ
  have so : Disjoint K.S O := disjoint_compl_right.mono_left Set.subset_union_left
  have to' : Disjoint K.T O := disjoint_compl_right.mono_left Set.subset_union_right
  have all : K.S∪K.T∪O=Set.univ := Set.union_compl_self _
  have ds := partition_handshake G K.S K.T O K.apart so to' all
  have dt := partition_handshake G K.T K.S O K.apart.symm to' so (by rw [Set.union_comm K.T K.S];exact all)
  have cross := cut_cross_union_right G O K.S K.T K.apart
  rw [crossCount_swap G O K.S,crossCount_swap G O K.T] at cross
  rw [crossCount_swap G K.S K.T] at ds
  change crossCount G K.rootsᶜ K.roots=_ at cross
  omega

theorem exact_handshake (cap:∀v,Nat.card (G.neighborSet v)≤10) (none:(oddRegularComponents G 10).ncard=0) :
    K.rootDefect K.S+K.rootDefect K.T+2*(G.induce K.S).edgeSet.ncard+2*(G.induce K.T).edgeSet.ncard+
      crossCount G K.supportᶜ K.roots+2*K.excessPairs+2*K.score=4 := by
  have total := K.root_degree_account
  have split := K.cut_partition
  have ports := K.total_ports cap none
  have ds := degree_sum_le_cap G K.S 10 (fun x _ => cap x)
  have dt := degree_sum_le_cap G K.T 10 (fun x _ => cap x)
  have score := K.actual
  rw [uniform_factor_cut_on_original] at score
  change (K.pieces.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-7*(K.T.ncard:ℤ)=(K.score:ℤ) at score
  have imbalance := K.imbalance
  dsimp only [rootDefect]
  omega

theorem core_is_full (cap:∀v,Nat.card (G.neighborSet v)≤10) : ∀x∈K.core,Nat.card (G.neighborSet x)=10 := by
  rintro _ ⟨v,rfl,mem⟩
  exact uniform_tight_piece_full G 3 7 cap K.S K.T _ mem v.val ⟨v,rfl,rfl⟩

theorem support_closed_of_no_external_root_edge (zero:crossCount G K.supportᶜ K.roots=0) :
    ∀x∈K.support,∀y,G.Adj x y → y∈K.support := by
  rintro x (a|j) y e
  · by_contra out;exact no_edge_when_port_zero G zero out a e.symm
  · obtain root|inside := regionCore_neighbor G K.roots K.pieces j e
    · obtain ⟨v,_,rfl⟩ := root;exact Or.inl v.property
    · exact Or.inr inside

#print axioms exact_handshake
#print axioms core_is_full
#print axioms support_closed_of_no_external_root_edge
end TenOuterCut
end JSP452Audit.StarHost
